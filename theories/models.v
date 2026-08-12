
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import RelationClasses.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
From HB Require Import structures.
From deriving Require Import deriving.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.DecidableClass.
Import Order.TTheory.
Open Scope order_scope.

Require Export NonInterference.theories.theorems.

(* =================================================================
   This file defines the process-scheduling models studied in the paper.

   It is organised so that everything the two designs share is defined
   once, before either design is named:

     Part I   (sections 0-7)   the shared skeleton, culminating in the
                               generic [model].  Nothing here is specific
                               to a design or to a concrete system.
     Part II  (sections 8-9)   the two designs, obtained by instantiating
                               [model] at the three parameters that differ
                               between them, plus the projected
                               [model_sliced_userview].
     Part III (sections 10-11) one concrete system -- userspace processes,
                               scheduler, handler length, slice size -- and
                               the example traces that exhibit its
                               behaviour.

   The three models:

     model_immediate       : Proc T_in (T_out' Opub Opriv)
       Normal interrupt handling: interrupts an attacker should not know
       about leak through scheduling.

     model_sliced          : Proc T_in (T_out' Opub Opriv)
       Interrupt masking is controlled so that secret interrupts can be
       received without leaking.  Shows every process-pool output (user
       space, scheduler and all handlers).

     model_sliced_userview : Proc T_in (T_out Opub Opriv)
       The final model: [model_sliced] behind a projection of the pool's
       output that erases every slot but the two user space processes.
       This is the one proved non-interfering in noninterference.v.

   Contents:
     Part I
       0.  Interfaces
       1.  Interrupt handler and the slot family
       2.  Process pool
       3.  Stateful wrapper
       4.  Model state
       5.  Reading the pool's output
       6.  State transitions
       7.  The generic model
     Part II
       8.  model_immediate and model_sliced, side by side
       9.  model_sliced_userview
     Part III
       10. A concrete system
       11. Adequacy: example traces
   ================================================================= *)

(* A note on notation.  Processes have type [Proc I O] where I and O range over
   the inductive [Ty] of interface types, and [ [t] ] denotes the Coq type that
   [t : Ty] encodes.  Indexing by [Ty] rather than by Coq's [Set] is what makes
   reductions invertible in the proofs, but it also forces the explicit [@] and
   [Ty] annotations below.  To keep the constructions readable, each process
   definition is preceded by a comment giving the same term with those
   annotations erased. *)


(* #################################################################
   PART I -- the shared skeleton
   ################################################################# *)

(* === 0. Interfaces === *)

Fixpoint times_n n (f : nat -> Ty) : Ty :=
  let t := f n in
  match n with
  | 0 => t
  | S n' => Times t (times_n n' f)
  end.
Definition times_on (n : nat) (f : nat -> Ty) := times_n n (Option \o f).


Definition T_in := TInterrupt.
(* [Opub] and [Opriv] are the alphabets of the public and the secret user
   process.  They are parameters throughout: the mechanism never inspects a
   user-slot value, only whether the slot produced one, so nothing below
   depends on what fills these two positions. *)
Definition T_out' (Opub Opriv : Ty) := Times (Option Opub) (Times (Option Opriv) (Times (Option Nat) (times_on 2 (fun _ => THandlerOutput)))).
Definition T_out (Opub Opriv : Ty) := Option (Sum Opub Opriv).

(* The concrete alphabets used by the instance of Part III. *)
Notation T_out'C := (T_out' TPublicOutput TTypeSyscall).
Notation T_outC := (T_out TPublicOutput TTypeSyscall).


(* === 1. Interrupt handler and the slot family === *)

Definition handler_type := Proc Empty THandlerOutput.

(* I_handler runtime =
     map id (fun o => if o.1 == 0 then Notify else Nothing)
       (sta (fun _ v => v) (fun _ v => v.+1 %% runtime) 0 (out tt))

   A handler counts modulo [runtime], emitting [Nothing] while the count is
   nonzero and [Notify] on the step that brings it back to 0 -- so it signals
   completion exactly every [runtime] output steps.  [runtime] is a parameter;
   what the design needs is only that every handler has the *same* one, so that
   a secret handler's run is the same length as the NOP run it replaces.
   ([runtime = 0] degenerates: [n %% 0 = n], so the count never returns to 0 and
   the handler never signals completion.) *)
Definition I_handler (runtime : nat) : handler_type :=
  map (O := Times Nat Unit) (O' := THandlerOutput) id
    (fun o => if o.1 == 0 then Notify else Nothing)
    (sta (V := Nat) (O := Unit)
       (fun _ v => v) (fun _ v => v.+1 %% runtime)
       0
       (out (O := Unit) tt)).

(* Only the secret user process consumes input (the disk handler's Notify).
   Every other slot is input-free, which the interface records as [Empty]. *)
Definition my_f_I (n : nat) :=
  match n with
  | 0 => Empty (*tI*)
  | 1 => Empty (*dI*)
  | 2 => Empty (*defaultI*)
  | 3 => Empty (*scheduler*)
  | 4 => THandlerOutput (*high*)
  | 5 => Empty (*low*)
  | _ => Empty (*padding*)
  end.

Definition my_f_O (Opub Opriv : Ty) (n : nat) :=
  match n with
  | 0 => THandlerOutput (*tI*)
  | 1 => THandlerOutput (*dI*)
  | 2 => THandlerOutput (*defaultI*)
  | 3 => Nat (*scheduler*)
  | 4 => Opriv (*high*)
  | 5 => Opub (*low*)
  | _ => Unit (*padding*)
  end.

(* unit_proc = out tt *)
Definition unit_proc : Proc Empty Unit := out (O := Unit) tt.

(* -- Indexed family of processes --

   The scheduler and the two user processes are parameters.  They are what
   the mechanism is supposed to protect, not part of the mechanism, so the
   development fixes only the handlers and the padding.  [slot_procs] places
   each parameter at the pid [my_f_pid] assigns it: the public process
   outermost (5), then the secret process (4), then the scheduler (3). *)
Definition slot_procs (runtime : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)             (*public user process, slot 5*)
  (p_priv : Proc THandlerOutput Opriv)  (*secret user process, slot 4*)
  (p_sched : Proc Empty Nat)            (*scheduler,           slot 3*)
  : forall n, Proc (my_f_I n) (my_f_O Opub Opriv n) :=
  fun n => match n with
           | 0        (*timer interrupt handler*)
           | 1        (*disk interrupt handler*)
           | 2        (*default handler*)
             => I_handler runtime
           | 3 => p_sched
           | 4 => p_priv
           | 5 => p_pub
           | _ => unit_proc (*padding*)
           end.


(* === 2. Process pool === *)

(* process_pool n f_initial f_I f_O f_proj f_pid f_proc =
     match n with
     | 0 =>
         map (fun i => (f_pid i.1 == 0, f_proj i.2 0)) id
           (swi (f_initial 0) (maybe (map id (fun o => (true, o)) (f_proc 0))))
     | n0.+1 =>
         par (map (fun i => (f_pid i.1 == n0.+1, f_proj i.2 n0.+1)) id
                (swi (f_initial n0.+1) (maybe (map id (fun o => (true, o)) (f_proc n0.+1)))))
             (process_pool n0 f_initial f_I f_O f_proj f_pid f_proc)
     end *)
Fixpoint process_pool
  (cur_pid : Ty)
  (n : nat)
  (f_initial : nat -> bool)
  (f_I f_O : nat -> Ty)
  (T' : Ty)
  (f_proj : [T'] -> forall n, [(Option (f_I n))])
  (f_pid : [cur_pid] -> [Nat])
  (f_proc : forall n, Proc (f_I n) (f_O n)) {struct n}
  : Proc (Times cur_pid T') (times_on n f_O) :=
  (* process n: gate the input by [f_pid = n], run [f_proc n] behind a switch, and
     par it with the pool for the remaining processes. *)
  match n as n1 return Proc (Times cur_pid T') (times_on n1 f_O) with
  | 0 =>
      map ((fun i => (f_pid i.1 == 0, f_proj i.2 0))
             : [Times cur_pid T'] -> [Times Bool (Option (f_I 0))]) id
          (swi (f_initial 0)
             (maybe (map id ((fun o => (true, o)) : [f_O 0] -> [Times Bool (f_O 0)]) (f_proc 0))))
  | n0.+1 =>
      par (map ((fun i => (f_pid i.1 == n0.+1, f_proj i.2 n0.+1))
                  : [Times cur_pid T'] -> [Times Bool (Option (f_I n0.+1))]) id
               (swi (f_initial n0.+1)
                  (maybe (map id ((fun o => (true, o)) : [f_O n0.+1] -> [Times Bool (f_O n0.+1)]) (f_proc n0.+1)))))
          (@process_pool cur_pid n0 f_initial f_I f_O T' f_proj f_pid f_proc)
  end.

Definition cur_pid := Sum Bool Nat.
Definition initial_pid : [cur_pid] := inr 3. (*starting with low process*)

Definition my_f_pid (pid : [cur_pid]) : [Nat] :=
  match pid with
  | inl true => 1 (*disk interrupt*)
  | inl false => 2 (*default interrupt*)
  | inr 0 => 0
  | inr 1 => 3
  | inr 2 => 4
  | inr 3 => 5
  | inr n => n
  end.

Definition my_f_initial (n : nat) := n == (my_f_pid initial_pid).

Definition T_intermediate := Option THandlerOutput.
Definition f_proj (i : [T_intermediate]) : forall n, [Option (my_f_I n)] :=
  fun n => match n with
           | 4 => i     (*the high process receives the disk-interrupt handler's output*)
           | _ => None  (*every other process receives nothing*)
           end.

(* pool p_pub p_priv p_sched =
     process_pool 5 my_f_initial my_f_I my_f_O T_intermediate f_proj my_f_pid
       (slot_procs p_pub p_priv p_sched) *)
Definition pool (runtime : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) :=
  @process_pool cur_pid 5 my_f_initial my_f_I (my_f_O Opub Opriv) T_intermediate f_proj my_f_pid
    (slot_procs runtime p_pub p_priv p_sched).


(* === 3. Stateful wrapper === *)

Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.
(*We define a stateful wrapper that will be wrapped around the process pool*)
(* reactive_system state state_update def p pool_input =
     map inl (inr_or_def def)
       (loop (map id snd
         (sta state_update (fun _ v => v) state
           (map pool_input inr (maybe p))))) *)
Definition reactive_system
  (cur_pid stateType : Ty)
  (state : [stateType])
  (T_in T_out T' : Ty)
  (state_update : [Sum T_in T_out] -> [stateType] -> [stateType])
  (def : [T_out])
  (p : Proc (Times cur_pid T') T_out)
  (pool_input : [Times stateType (Sum T_in T_out)] -> [Option (Times cur_pid T')])
  : Proc T_in T_out :=
  (@map T_in (Sum T_in T_out) (Sum T_in T_out) T_out inl (inr_or_def def)
                          (@loop (Sum T_in T_out)
                             (@map _ _ (Times _ _) _
                                id snd
                                (@sta _ _ stateType state_update (fun _ v => v) state
                                   (@map (Times stateType (Sum _ _ ))
                                      (Option (Times cur_pid T')) _ (Sum T_in T_out) pool_input inr (maybe p)))))).


(* === 4. Model state === *)
Definition mask := Bool.
Definition pending := Bool.
Definition I_bits := Times pending mask.
Definition ir_count := Option Nat.
Definition ic := Times I_bits (Times I_bits I_bits).
Definition count := Nat.
Definition re_sch := Bool.
Definition prev_pid := Option Nat.
Definition pids := Times cur_pid prev_pid.
(* ic_count bundles the interrupt-handler time slice with the interrupt controller.
   ir_count = None  -> feature disabled
   ir_count = Some n -> n steps of handler execution left; Some 0 -> return to user space *)
Definition ic_count := Times ir_count ic.
Definition bool_state := Times re_sch ic_count.
Definition all_interrupts : seq [TInterrupt] :=
  [:: TimerInterrupt; DiskInterrupt; DefaultInterrupt].
Definition sans_timer : seq [TInterrupt] :=
  [:: DiskInterrupt; DefaultInterrupt].
Definition stateType := Times pids bool_state.

Definition get_pids (v : [stateType]) := v.1.
Definition get_bool_state (v : [stateType]) := v.2.
Definition get_cur_pid (v : [stateType]) := (get_pids v).1.
Definition get_prev_pid (v : [stateType]) := (get_pids v).2.
Definition get_re_sch (v : [stateType]) := (get_bool_state v).1.
Definition get_ic_count (v : [stateType]) := (get_bool_state v).2.
Definition get_ir_count (v : [stateType]) := (get_ic_count v).1.
Definition get_ic (v : [stateType]) := (get_ic_count v).2.

Definition get_I_bits' (ic : [ic]) (ir : [TInterrupt]) : [I_bits] :=
  match ir with
  | DefaultInterrupt => ic.1
  | DiskInterrupt    => ic.2.1
  | TimerInterrupt => ic.2.2
  end.
Definition get_I_bits (v : [stateType]) (ir : [TInterrupt]) := get_I_bits' (get_ic v) ir.

Definition get_pending' (bits : [I_bits]) := bits.1.
Definition get_mask' (bits : [I_bits]) := bits.2.

Definition get_I_pending (v : [stateType]) (ir : [TInterrupt]) := get_pending' (get_I_bits v ir).
Definition get_I_mask (v : [stateType]) (ir : [TInterrupt]) := get_mask' (get_I_bits v ir).

Definition update_pids (v : [stateType]) pids : [stateType] := (pids,v.2).
Definition update_bool_state (v : [stateType]) bs : [stateType] := (v.1,bs).
Definition update_cur_pid (v : [stateType]) cur_pid : [stateType] := update_pids v (cur_pid,(get_pids v).2).
Definition update_prev_pid (v : [stateType]) prev_pid : [stateType] := update_pids v ((get_pids v).1,prev_pid).
Definition update_re_sch (v : [stateType]) re_sch : [stateType] := update_bool_state v (re_sch,(get_bool_state v).2).

Definition update_I_bits' (myic : [ic]) (ir : [TInterrupt]) (bits : [I_bits]) : [ic] :=
  match ir with
  | DefaultInterrupt => (bits, myic.2)
  | DiskInterrupt    => (myic.1, (bits, myic.2.2))
  | TimerInterrupt => (myic.1, (myic.2.1, bits))
  end.

Definition update_ic_count (v : [stateType]) icc : [stateType] := update_bool_state v ((get_bool_state v).1,icc).
Definition update_ir_count (v : [stateType]) c : [stateType] := update_ic_count v (c,(get_ic_count v).2).
Definition update_ic (v : [stateType]) ic : [stateType] := update_ic_count v ((get_ic_count v).1,ic).
Definition update_I_bits (v : [stateType]) (ir : [TInterrupt]) (bits : [I_bits]) := update_ic v (update_I_bits' (get_ic v) ir bits).

Definition update_I_pending (v : [stateType]) (ir : [TInterrupt]) pending : [stateType] :=
  update_I_bits v ir (pending,get_I_mask v ir).
Definition update_I_mask (v : [stateType]) (ir : [TInterrupt ]) mask : [stateType] :=
  update_I_bits v ir (get_I_pending v ir,mask).

Definition or_I_bits (b1 b2 : [I_bits]) : [I_bits] := (b1.1 || b2.1, b1.2 || b2.2).
Definition or_ic (c1 c2 : [ic]) : [ic] :=
  (or_I_bits c1.1  c2.1,
   (or_I_bits c1.2.1 c2.2.1,
    or_I_bits c1.2.2 c2.2.2)).
(* keep the base state's time slice (s1.2.1); only the interrupt controller is merged *)
Definition or_bool_state (s1 s2 : [bool_state]) : [bool_state] := (s1.1 || s2.1, (s1.2.1, or_ic s1.2.2 s2.2.2)).

Definition set_masks (v : [stateType]) : [stateType] :=
  foldr (fun I v' => update_I_mask v' I true) v all_interrupts.
Definition unset_masks (v : [stateType]) : [stateType] :=
  foldr (fun I v' => update_I_mask v' I false) v all_interrupts.
Definition unset_masks_sans (v : [stateType]) : [stateType] :=
  foldr (fun I v' => update_I_mask v' I false) v sans_timer.
Definition unset_tI (v : [stateType]) : [stateType] := update_I_mask v TimerInterrupt false.
Definition set_tI (v : [stateType]) : [stateType] := update_I_mask v TimerInterrupt true.
Definition set_otherIs (v : [stateType]) : [stateType] := foldr (fun I v' => update_I_mask v' I true) v sans_timer.
Definition masks_set (v : [stateType]) :=
  foldr (fun I b => (get_I_mask v I) && b) true all_interrupts.


(* === 5. Reading the pool's output ===

   Slot accessors and the two projections that leave the pool: [def], the output
   emitted when no slot produced one, and [pool_input], the value fed back in.
   Both designs use all of these unchanged. *)

Definition tI_out (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) :=
  match o with
  | (_,(_,(_,(_,(_,x))))) => x
  end.

Definition dI_out (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) :=
  match o with
  | (_,(_,(_,(_,(x,_))))) => x
  end.

Definition default_I_out (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) :=
  match o with
  | (_,(_,(_,(x,(_,_))))) => x
  end.

Definition is_I_out_done (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) : [Option TInterrupt] :=
  if tI_out o is Some Notify then Some TimerInterrupt
  else if dI_out o is Some Notify then Some DiskInterrupt
  else if default_I_out o is Some Notify then Some DefaultInterrupt
  else None.

Definition def (Opub Opriv : Ty) : [ T_out' Opub Opriv ]  := (None,(None,(None,(None,(None,None))))).

(*discards input from the inner process, only allowed to affect bit in ic, not pid*)
Definition pool_input (Opub Opriv : Ty) (si : [Times stateType (Sum T_in (T_out' Opub Opriv))]) : [Option (Times cur_pid T_intermediate)] :=
  if si.2 is inr o then Some (get_cur_pid si.1, dI_out o) else None.

(* The user view: keep the two user slots, erase the scheduler and all three
   handlers.  Used by [model_sliced_userview] in section 9. *)
Definition parse_output (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) : [T_out Opub Opriv] :=
  match o with
  | (Some public,_) => Some (inl public)
  | (None,(Some prv,_)) => Some (inr prv)
  | _ => None
  end.


(* === 6. State transitions === *)
Definition step_left (Opub Opriv : Ty) (f : [T_in] -> [stateType] -> [stateType]) : [Sum T_in (T_out' Opub Opriv)] -> [stateType] -> [stateType] :=
  fun i v =>
  match i with
  | inl i => f i v
  | inr _ => v
  end.

Definition step_right (Opub Opriv : Ty) (f : [T_out' Opub Opriv] -> [stateType] -> [stateType]) : [Sum T_in (T_out' Opub Opriv)] -> [stateType] -> [stateType] :=
  fun i v =>
  match i with
  | inl _ => v
  | inr o => f o v
  end.

(* An arriving interrupt is recorded as pending; whether it is serviced is
   decided later, by [initiate_next]. *)
Definition record_pending (Opub Opriv : Ty) := @step_left Opub Opriv (fun i v => update_I_pending v i true).

Definition is_sch_out (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) :=
  match o with
  | (None,(None,(Some n,_))) => Some n
  | _ => None
  end.
Definition check_scheduler (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) (v : [stateType])  :=
  if is_sch_out o is Some n then update_cur_pid v (inr n) else v.

(* A scheduler output installs the pid it names as the current one.  Note this
   reads the scheduler slot only -- the user slots are inspected for None-ness and
   nothing more (see [is_sch_out]), which is what keeps the state transition
   independent of what userspace does. *)
Definition apply_schedule (Opub Opriv : Ty) := step_right (@check_scheduler Opub Opriv).

Definition nat_to_cur_pid (n : nat) : [cur_pid ] :=
  match n with
  | 0 => inr 0 (*timer interrupt*)
  | 1 => inl true (*disk interrupt*)
  | 2 => inl false (*default interrupt*)
  | 3 => inr 1 (*scheduler*)
  | 4 => inr 2 (*high p*)
  | 5 => inr 3 (*low p*)
  | n => inr n
  end.
Definition I_handler_pid (ir : [TInterrupt]) : [cur_pid] :=
  nat_to_cur_pid (index ir all_interrupts).

(* before overriding cur_pid, save it to prev_pid if it is a user process *)
Definition save_cur_to_prev (v : [stateType]) : [stateType] :=
  if get_cur_pid v is inr n
  then update_prev_pid v (Some n)
  else v.

Definition initiate_handler (ir : [TInterrupt]) (v : [stateType]) :=
  update_I_pending (set_masks (update_cur_pid (save_cur_to_prev v) (I_handler_pid ir))) ir false.

(* a handler is selectable iff pending and not masked *)
Definition I_ready (v : [stateType]) (ir : [TInterrupt]) : bool :=
  get_I_pending v ir && ~~ get_I_mask v ir.

Definition first_ready (v : [stateType]) : option [TInterrupt] :=
  ohead [seq ir <-  all_interrupts | (I_ready v ir) ].

Definition is_handler_pid (v : [stateType]) :=
    match get_cur_pid v with
    | inr 0 => true
    | inr _ => false
    | _ => true
    end.

Definition scheduler_pid : [cur_pid] := inr 1.

Definition initiate_scheduler  (v : [stateType]) := update_re_sch (update_prev_pid (update_cur_pid v scheduler_pid) None) false.

Definition get_prev_pid_wrap (v : [stateType]) : [Option cur_pid] := if get_prev_pid v is Some n then Some (inr n) else None.
Definition initiate_prev_pid  (v : [stateType]) := update_prev_pid (update_cur_pid v (odflt scheduler_pid (get_prev_pid_wrap v))) None.

Definition initiate_next (enforce_invariant :  [stateType] -> [stateType]) :  [stateType] -> [stateType] :=
  fun v => if (masks_set v) then v (*handler running*) else
             let v := enforce_invariant v (*apply time slice logic to bools*) in
             if first_ready v is Some ir then initiate_handler ir v (*first or later handler in the time slice is initiated here, enforced that at least one will run due to enforce_invariant*) else
               if is_handler_pid v then if get_re_sch v then initiate_scheduler v else initiate_prev_pid v  (*mask not set but we are in handler pid, we have just finished the time slice*) else
                 v (*we are running in user space*).



Definition state_step (Opub Opriv : Ty) (handler_preroutine : [T_out' Opub Opriv] -> [stateType] -> [stateType]) (enforce_invariant : [stateType] -> [stateType]) (i : [Sum T_in (T_out' Opub Opriv)]) : [stateType] -> [stateType] :=
  (@step_right Opub Opriv (fun i => initiate_next enforce_invariant) i) \o (step_right handler_preroutine i) \o (apply_schedule i) \o (record_pending i).
(*we wrap initiate_next in step_right even though it does not use the input to ensure we only apply this step on output updates, this is important for the last case of f_EP for initiate_next*)


(* === 7. The generic model ===

   Everything above is shared.  A model is the process pool run inside the
   stateful wrapper, and the only freedom left is the triple

     (init, handler_preroutine, enforce_invariant)

   that section 8 fixes in two different ways.  Note [runs] is not a parameter
   here: the slice size reaches the model only through [handler_preroutine],
   already applied. *)
Definition model (runtime : nat) (Opub Opriv : Ty)
  (init : [stateType])
  (handler_preroutine : [T_out' Opub Opriv] -> [stateType] -> [stateType])
  (enforce_invariant : [stateType] -> [stateType])
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out' Opub Opriv) :=
  @reactive_system cur_pid stateType init T_in (T_out' Opub Opriv) T_intermediate
    (state_step handler_preroutine enforce_invariant) (def Opub Opriv)
    (pool runtime p_pub p_priv p_sched) (@pool_input Opub Opriv).


(* #################################################################
   PART II -- the two designs
   ################################################################# *)

(* === 8. model_immediate and model_sliced, side by side ===

   The two designs are the same [model] at two different triples, and that
   difference is the whole security story:

     parameter            model_immediate            model_sliced
     -----------------------------------------------------------------------
     initial state        initial_state_immediate    initial_state_sliced
                          no slice, no masks set     slice at [Some 0], every
                                                     mask but the timer's set
     handler preroutine   immediate_preroutine       sliced_preroutine runtime runs
                          a finished handler         a finished timer handler opens
                          unmasks everything, so     a slice; the slice is counted
                          a pending interrupt is     down and closed on a handler
                          serviced at once           boundary
     enforce_invariant          id                         enforce_invariant
                          nothing                    off-slice, forces the disk and
                                                     default handlers masked

   In [model_immediate] a secret interrupt is therefore serviced the moment it
   arrives, displacing whatever was running; in [model_sliced] it can only be
   serviced inside a slice, where it replaces a NOP handler run of the same
   length. *)

(* -- model_immediate -- *)

Definition false_I_bits : [I_bits] := (false,false).
Definition false_ic : [ic] := ((false,false),(false_I_bits,false_I_bits)).
Definition initial_state_immediate : [stateType] := ((initial_pid,None),(false,(None,false_ic))).

Definition immediate_preroutine (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) (v : [stateType])  :=
  if is_I_out_done o is Some ir then let v := unset_masks v in if ir is TimerInterrupt then update_re_sch v true else v else v.

(* model_immediate p_pub p_priv p_sched =
     model initial_state_immediate immediate_preroutine id p_pub p_priv p_sched *)
Definition model_immediate (runtime : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out' Opub Opriv) :=
  model runtime initial_state_immediate (@immediate_preroutine Opub Opriv) id
    p_pub p_priv p_sched.

(* -- model_sliced -- *)

Definition mask_most : [ic] := ((false,true),((false,true),(false,false))). (*mask set for everything but timer interrupt*)

Definition initial_state_sliced : [stateType] := ((initial_pid,None),(false,(Some 0,mask_most))).

(* The time slice, as a whole number [runs] of handler runs.  Expressing it this
   way rather than as an independent constant is what makes "the slice ends on a
   handler boundary" structural instead of a side condition: [handler_completed]
   can then *compute* the boundaries as the nonzero multiples of [runtime]. *)
Definition time_slice (runtime runs : nat) := runs * runtime.

Definition handler_completed (runtime : nat) (c : [ir_count]) :=
  match c with
  | Some n => (n != 0) && (n %% runtime == 0)
  | None => false
  end.

Definition initiate_ir (runtime runs : nat) (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) (v : [stateType]) : [stateType] :=
  if tI_out o is Some Notify then update_ir_count v (Some (time_slice runtime runs)) else v.

Definition check_handler_completed (runtime : nat) (v : [stateType]) : [stateType] :=
  if handler_completed runtime (get_ir_count v) then set_tI (unset_masks v) else v.

Definition check_ir_count (v : [stateType]) : [stateType] :=
    match (get_ir_count v) with
    | Some n.+1 => update_ir_count v (Some n)
    | Some 0 => update_ir_count (set_otherIs (unset_tI v)) None
    | None => v
    end.

Definition timeslice_live (c : [ir_count]) := match c with | Some n => 0 < n | _ => false end.

(*If timeslice is not live, we enforce that disk and default handlers are masked, and pending default is false.
 This allows us to infer that for v and v' that are related, that if v is ready as disk handler or default, then v' will also be ready.
 The reasoning chain is:
v is ready -> time slice is live for v -> time slice is live for v' -> pending for default is true (which combined with unset_handler_masks invariant that it always turns off masks when a handler is done, ensures that default handler always can fire if v can fire disk or default handler
 *)

Definition enforce_invariant v := let b := timeslice_live (get_ir_count v) in
                            let ic := (true,(None,((b,~~b),((false,~~b),(false,b))))) in
                            let v := update_bool_state v (or_bool_state (get_bool_state v) ic) in
                            let m := get_I_mask v DiskInterrupt in
                            update_I_mask v DefaultInterrupt m.

Definition sliced_preroutine (runtime runs : nat) (Opub Opriv : Ty) (o : [T_out' Opub Opriv]) : [stateType] -> [stateType] := check_ir_count \o check_handler_completed runtime \o (initiate_ir runtime runs o). (*\o (unset_handler_masks o)*)

(* model_sliced p_pub p_priv p_sched =
     model initial_state_sliced (sliced_preroutine runtime runs) enforce_invariant
       p_pub p_priv p_sched *)
Definition model_sliced (runtime runs : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out' Opub Opriv) :=
  model runtime initial_state_sliced (@sliced_preroutine runtime runs Opub Opriv) enforce_invariant
    p_pub p_priv p_sched.


(* === 9. model_sliced_userview === *)

Definition model_sliced_userview (runtime runs : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out Opub Opriv) :=
  map id (@parse_output Opub Opriv) (model_sliced runtime runs p_pub p_priv p_sched).

Definition final_out_rel (Opub Opriv : Ty) : cRel [T_out Opub Opriv] := eqmaybe_false (eqsum (publicRel Opub) (privateRel Opriv)).


(* #################################################################
   PART III -- one concrete system
   ################################################################# *)

(* === 10. A concrete system ===

   Nothing in Parts I and II names a user process, a scheduler, a handler
   length or a slice size.  This section supplies one of each, so that the
   models can be run and their behaviour exhibited as traces. *)

(* low_p = out GetRequest *)
Definition low_p := @out Empty TPublicOutput GetRequest.


(* alternate x y z pred =
     map inl (fun o => if o is inr (true, _) then x else y)
       (loop (map id inr
         (sta (fun i v => if i is inl i' then v || pred i' else false)
              (fun o v => v) false
              (out z)))) *)
Definition alternate (A B C : Ty) (x y : [B]) (z : [C]) (pred : [A] -> bool) :=
  @map _ (Sum _ _) (Sum _ (Times Bool C)) B
                        inl
                        (fun o => if o is inr (true,z) then x else y)
                        (@loop (Sum A (Times Bool C))
                        (@map (Sum A _) _ _ (Sum _ _) id (fun o => inr o)
                        ((@sta (Sum _ _) _ Bool
                           (fun i v => match i with | inl i' => v || pred i' | _ => false end)
                           (fun o v => v)
                           false
                           (@out (Times Bool _ ) C z)
                        )))).
(* high_p = alternate Syscall NOP tt (fun i => i == Notify) *)
Definition high_p := @alternate THandlerOutput TTypeSyscall Unit Syscall NOP tt (fun i => i == Notify).

(* scheduler =
     map id (fun o => o.1 + 2)
       (sta (fun _ v => v) (fun _ v => v.+1 %% 2) 1 (out tt)) *)
Definition scheduler : Proc Empty Nat :=
  map (O := Times Nat Unit) (O' := Nat) id
    (fun o => o.1 + 2)                        (*skip the interrupt handlers to reach high_p and low_p*)
    (sta (V := Nat) (O := Unit)
       (fun _ v => v) (fun _ v => v.+1 %% 2)
       1                                      (*will start scheduling the high process*)
       (out (O := Unit) tt)).

(* The concrete handler length and slice: handlers two output steps long, a
   slice of two handler runs. *)
Definition handler_runtime := 2.
Definition slice_runs := 2.

Definition my_procs := slot_procs handler_runtime low_p high_p scheduler.
Definition my_process_pool := pool handler_runtime low_p high_p scheduler.

Definition model_immediate_concrete := model_immediate handler_runtime low_p high_p scheduler.
Definition model_sliced_concrete := model_sliced handler_runtime slice_runs low_p high_p scheduler.
Definition model_sliced_userview_concrete :=
  model_sliced_userview handler_runtime slice_runs low_p high_p scheduler.

(* Sanity, at this instance: the computed test agrees with the enumeration
   [Some 2 | Some 4] it replaced, on every value the counter can reach (the
   counter starts at [time_slice] and is decremented to [Some 0] before being
   cleared). *)
Lemma handler_completed_reachable n :
  n <= time_slice handler_runtime slice_runs ->
  handler_completed handler_runtime (Some n) = ((n == 2) || (n == 4)).
Proof. by case: n => [|[|[|[|[|n]]]]]. Qed.


(* === 11. Adequacy: example traces ===

   Each model is exercised on two runs of the concrete system: one with no disk
   interrupt and one with a disk interrupt arriving at the same point.  Reading
   the two [model_immediate] traces against each other shows the leak -- the
   public process loses output steps to the handler -- and the two
   [model_sliced] traces show that it is gone.  The [model_sliced_userview]
   traces are the [model_sliced] ones under [parse_output]. *)

(* -- Named inputs and outputs -- *)
Definition Tsum' := ([T_in] + [T_out'C])%type.
Definition Tsum := Sum T_in T_outC.

Definition dI' : Tsum' := inl DiskInterrupt.
Definition tI' : Tsum' := inl TimerInterrupt.
Definition low_out x : [T_out'C] := (Some x,(None,(None,(None,(None,None))))).
Definition high_out x : [T_out'C] := (None,(Some x,(None,(None,(None,None))))).
Definition sch_o x : [T_out'C] := (None,(None,(Some x,(None,(None,None))))).
Definition defaultI_o x : [T_out'C] := (None,(None,(None,(Some x,(None,None))))).
Definition dI_o x : [T_out'C] := (None,(None,(None,(None,(Some x,None))))).
Definition tI_o x : [T_out'C] := (None,(None,(None,(None,(None,Some x))))).

Definition tmr_done' : Tsum' :=  inr (tI_o (Notify)).
Definition tmr_step' : Tsum' :=  inr (tI_o (Nothing)).

Definition dsk_done' : Tsum' :=  inr (dI_o (Notify)).
Definition dsk_step' : Tsum' :=  inr (dI_o (Nothing)).

Definition out_get' : Tsum' := inr (low_out GetRequest).
Definition out_nop' : Tsum' := inr (high_out NOP).
Definition out_syscall' : Tsum' := inr (high_out Syscall).

Definition sched_pub' : Tsum' := inr (sch_o 3).
Definition sched_priv' : Tsum' := inr (sch_o 2).

Definition nop_step' : Tsum' :=  inr (defaultI_o (Nothing)).
Definition nop_done' : Tsum' :=  inr (defaultI_o (Notify)).

Definition out_get : [Tsum] := inr (Some (inl (GetRequest))).
Definition out_nop : [Tsum] := inr (Some (inr NOP)).
Definition out_syscall : [Tsum] := inr (Some (inr Syscall)).
Definition w_None : [Tsum] := inr None.
Definition tI : [Tsum] := inl TimerInterrupt.
Definition dI : [Tsum] := inl DiskInterrupt.

Definition seqtype' := seq Tsum'.
Definition seqtype := seq ([T_in] + [T_outC]).


(* -- model_immediate traces -- *)
Definition immediate_no_dI' : seqtype' :=   [::out_get';                                     tI';out_get';tmr_step';tmr_done';sched_priv';out_nop'(*nop*);tI';out_nop';tmr_step';tmr_done';sched_pub';out_get'].
Definition immediate_with_dI' : seqtype' := [::out_get';dI';out_get';dsk_step';dsk_done';out_get';tI';out_get';tmr_step';tmr_done';sched_priv';out_syscall'(*sys*);tI';out_nop';tmr_step';tmr_done';sched_pub';out_get'].

Ltac rewr := rewrite /model_immediate_concrete /model_immediate /model /reactive_system /my_process_pool /pool /process_pool /my_f_initial /low_p /alternate /high_p /pool_input /tI_o /I_handler /f_proj /scheduler /low_out.

Ltac lsolv := try solve [ reduce_tac;reduce_tac | reduce_tac;try solve [reduce_once | econ];simpl;first (reduce_tac;reduce_tac)];simpl.
Ltac reduce_tac2 :=
  (try rewr);
   (repeat
      reduce_once);(try swi_instans); rewrite ?eqxx /= /xor /=.

Ltac sta_state_reduce :=
  match goal with
  | |- context [(@sta (Sum T_in T_out'C) (Sum T_in T_out'C) stateType (state_step _ _) _ ?state _)] =>let reduced := eval cbv in state in
                                                                                                          pattern state; match goal with |- ?F state => change (F reduced) end; cbv beta
  end.

Lemma trace_immediate_no_dI' : forall l, Trace (publicRel _) l immediate_no_dI' model_immediate_concrete.
Proof.
  intros.
  rewr;simpl;rewr;simpl;rewr;simpl;rewr.

  sta_state_reduce.

   do 12 (first [econ;[idtac | econ | idtac] | econ];
         reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).

  (*proved the last element of the trace manually to avoid evar holes in proof*)
   (first [econ;[idtac | econ | idtac] | econ];
    reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans).
   econ. reduce_tac2;reduce_tac2. econ. econ. reduce_tac. econ. econ.
   reduce_tac. econ. econ. reduce_tac. econ. econ. reduce_tac. econ.
   econ. reduce_tac. econ. econ. reduce_tac. econ.
Qed.

Lemma trace_immediate_with_dI' : forall l, Trace (publicRel _) l immediate_with_dI' model_immediate_concrete.
Proof.
  intros.
  rewr;simpl;rewr;simpl;rewr;simpl;rewr.

  do 17(first [econ;[idtac | econ | idtac] | econ];
        reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).

  (*proved the last element of the trace manually to avoid evar holes in proof*)
   (first [econ;[idtac | econ | idtac] | econ];
    reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans).
   econ. reduce_tac2;reduce_tac2. econ. econ. reduce_tac. econ. econ.
   reduce_tac. econ. econ. reduce_tac. econ. econ. reduce_tac. econ.
   econ. reduce_tac. econ. econ. reduce_tac. econ.
Qed.


(* -- model_sliced traces -- *)
Definition sliced_no_dI' : seqtype' :=   [::out_get';                      tI';out_get';tmr_step';tmr_done';nop_step';nop_done';nop_step';nop_done';sched_priv';out_nop'(*nop*);tI';out_nop';tmr_step';tmr_done';nop_step';nop_done';nop_step';nop_done';sched_pub';out_get'].
Definition sliced_with_dI' : seqtype' := [::out_get';dI';out_get';out_get';tI';out_get';tmr_step';tmr_done';dsk_step'      ;dsk_done'      ;nop_step';nop_done';sched_priv';out_syscall'(*sys*);tI';out_nop';tmr_step';tmr_done';nop_step';nop_done';nop_step';nop_done';sched_pub';out_get'].


Ltac rewr ::= rewrite /model_immediate_concrete /model_immediate /model /reactive_system /my_process_pool /pool /process_pool /my_f_initial /low_p /alternate /high_p /pool_input /tI_o /I_handler /f_proj /scheduler /low_out /model_sliced_concrete /model_sliced /my_process_pool /pool /pool_input /f_proj.

Lemma trace_sliced_no_dI' : forall l, Trace (publicRel _) l sliced_no_dI' model_sliced_concrete.
Proof.
  intros.
  rewr;simpl;rewr;simpl;rewr;simpl;rewr.

  do 20(first [econ;[idtac | econ | idtac] | econ];
        reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).

   (first [econ;[idtac | econ | idtac] | econ];
    reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans).
   econ. reduce_tac2;reduce_tac2. econ. econ. reduce_tac. econ. econ.
   reduce_tac. econ. econ. reduce_tac. econ. econ. reduce_tac. econ.
   econ. reduce_tac. econ. econ. reduce_tac. econ.
Qed.

Lemma trace_sliced_with_dI' : forall l, Trace (publicRel _) l sliced_with_dI' model_sliced_concrete.
Proof.
  intros.
  rewr;simpl;rewr;simpl;rewr;simpl;rewr.

  do 23(first [econ;[idtac | econ | idtac] | econ];
        reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).

   (first [econ;[idtac | econ | idtac] | econ];
    reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans).
   econ. reduce_tac2;reduce_tac2. econ. econ. reduce_tac. econ. econ.
   reduce_tac. econ. econ. reduce_tac. econ. econ. reduce_tac. econ.
   econ. reduce_tac. econ. econ. reduce_tac. econ.
Qed.


(* -- model_sliced_userview traces -- *)

Definition map_tr (I O O' : Ty) (f : [O] -> [O']) (s : seq ([I] + [O])) := seq.map (fun x => match x with | inl x' => inl x' | inr y => inr (f y) end) s.
Lemma Trace_map : forall (A B B' : Ty) (p : Proc A B) (f : [B] -> [B']) (s : seq ([A] + [B])) (BRel : cRel [B]) (BRel' : cRel [B']) l,
    f_NI BRel BRel' f ->
    Trace BRel l s p -> Trace BRel' l (map_tr f s) (map id f p).
Proof.
  intros.
  elim : H0;ssa.
  econ. econ. econ. eauto. done.
  econ. econ. econ. eauto. apply H. done. done.
Qed.


Definition good_no_dI : seqtype :=   [::out_get;                      tI;out_get;w_None;w_None;w_None;w_None;w_None;w_None;w_None;out_nop(*nop*);tI;out_nop;w_None;w_None;w_None;w_None;w_None;w_None;w_None;out_get].
Definition good_with_dI : seqtype := [::out_get;dI;out_get;out_get;tI;out_get;w_None;w_None;w_None      ;w_None      ;w_None;w_None;w_None;out_syscall(*sys*);tI;out_nop;w_None;w_None;w_None;w_None;w_None;w_None;w_None;out_get].

Lemma good_no_dI_eq : map_tr (@parse_output TPublicOutput TTypeSyscall) sliced_no_dI' = good_no_dI.
Proof. ssa. Qed.

Lemma good_with_dI_eq : map_tr (@parse_output TPublicOutput TTypeSyscall) sliced_with_dI' = good_with_dI.
Proof. ssa. Qed.

Lemma trace_no_dI : forall l, Trace (publicRel _) l good_no_dI model_sliced_userview_concrete.
Proof.
  intros. rewrite -good_no_dI_eq. eapply Trace_map.
  2:eapply trace_sliced_no_dI'.
  mrw. ssa. subst. done.
Qed.

Lemma trace_with_dI : forall l, Trace (publicRel _) l good_with_dI model_sliced_userview_concrete.
Proof.
  intros. rewrite -good_with_dI_eq. eapply Trace_map.
  2:eapply trace_sliced_with_dI'.
  mrw. ssa. subst. done.
Qed.

