
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import RelationClasses.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
From HB Require Import structures.
From deriving Require Import deriving.
Require Import Coq.Classes.DecidableClass.
Import Order.TTheory.
Open Scope order_scope.

Require Export NonInterference.theories.theorems.

(* =================================================================
   This file defines the process-scheduling models studied in the paper.

   It is organised so that everything the two interrupt policies share is
   defined once, before either policy is named:

     Part I   (sections 0-7)   the shared skeleton, culminating in the
                               generic [model].  Nothing here is specific
                               to a policy or to a concrete system.
     Part II  (sections 8-9)   the two interrupt policies, obtained by
                               instantiating [model] at the three parameters
                               that differ between them, plus the projected
                               [model_sliced_userview].
     Part III (sections 10-11) one concrete system -- userspace processes,
                               scheduler, handler length, slice size -- and
                               the example traces that exhibit its
                               behaviour.

   The three models:

     model_immediate       : Proc T_in (T_out Opub Opriv)
       Normal interrupt handling: interrupts an attacker should not know
       about leak through scheduling.

     model_sliced          : Proc T_in (T_out Opub Opriv)
       Interrupt masking is controlled so that secret interrupts can be
       received without leaking.  Shows every process-pool output (user
       space, scheduler and all handlers).

     model_sliced_userview : Proc T_in (T_out_userview Opub Opriv)
       The final model: [model_sliced] behind a projection of the pool's
       output that erases every slot but the two user space processes.
       This is the one proved non-interfering in noninterference.v.

   Contents:
     Part I
       0.  Input and output types
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
   the inductive [Ty], and [ [t] ] denotes the Coq type that
   [t : Ty] encodes.  Indexing by [Ty] rather than by Coq's [Set] is what makes
   reductions invertible in the proofs, but it also forces the explicit [@] and
   [Ty] annotations below.  To keep the constructions readable, each process
   definition is preceded by a comment giving the same term with those
   annotations erased. *)


(* #################################################################
   PART I -- the shared skeleton
   ################################################################# *)

(* === 0. Input and output types === *)

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
Definition T_out (Opub Opriv : Ty) := Times (Option Opub) (Times (Option Opriv) (Times (Option Nat) (times_on 2 (fun _ => THandlerOutput)))).
Definition T_out_userview (Opub Opriv : Ty) := Option (Sum Opub Opriv).

(* The concrete alphabets used by the instance of Part III. *)
Notation T_outC := (T_out TPublicOutput TTypeSyscall).
Notation T_out_userviewC := (T_out_userview TPublicOutput TTypeSyscall).


(* === 1. Interrupt handler and the slot family === *)

Definition handler_type := Proc Empty THandlerOutput.

(* ir_handler runtime =
     map id (fun o => if o.1 == 0 then Notify else Nothing)
       (sta (fun _ v => v) (fun _ v => v.+1 %% runtime) 0 (out tt))

   A handler counts modulo [runtime], emitting [Nothing] while the count is
   nonzero and [Notify] on the step that brings it back to 0 -- so it signals
   completion exactly every [runtime] output steps.  [runtime] is a parameter;
   what the sliced policy needs is only that every handler has the *same* one, so that
   a secret handler's run is the same length as the NOP run it replaces.
   ([runtime = 0] degenerates: [n %% 0 = n], so the count never returns to 0 and
   the handler never signals completion.) *)
Definition ir_handler (runtime : nat) : handler_type :=
  map (O := Times Nat Unit) (O' := THandlerOutput) id
    (fun o => if o.1 == 0 then Notify else Nothing)
    (sta (V := Nat) (O := Unit)
       (fun _ v => v) (fun _ v => v.+1 %% runtime)
       0
       (out (O := Unit) tt)).

(* Only the secret user process consumes input (the disk handler's Notify).
   Every other slot is input-free, which the input type records as [Empty]. *)
Definition slot_I (n : nat) :=
  match n with
  | 0 => Empty (*tI*)
  | 1 => Empty (*dI*)
  | 2 => Empty (*NOP handler*)
  | 3 => Empty (*scheduler*)
  | 4 => THandlerOutput (*high*)
  | 5 => Empty (*low*)
  | _ => Empty (*padding*)
  end.

Definition slot_O (Opub Opriv : Ty) (n : nat) :=
  match n with
  | 0 => THandlerOutput (*tI*)
  | 1 => THandlerOutput (*dI*)
  | 2 => THandlerOutput (*NOP handler*)
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
   each parameter at the pid [slot_pid] assigns it: the public process
   outermost (5), then the secret process (4), then the scheduler (3). *)
Definition slot_procs (runtime : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)             (*public user process, slot 5*)
  (p_priv : Proc THandlerOutput Opriv)  (*secret user process, slot 4*)
  (p_sched : Proc Empty Nat)            (*scheduler,           slot 3*)
  : forall n, Proc (slot_I n) (slot_O Opub Opriv n) :=
  fun n => match n with
           | 0        (*timer interrupt handler*)
           | 1        (*disk interrupt handler*)
           | 2        (*NOP handler*)
             => ir_handler runtime
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

Definition slot_pid (pid : [cur_pid]) : [Nat] :=
  match pid with
  | inl true => 1 (*disk interrupt*)
  | inl false => 2 (*NOP handler*)
  | inr 0 => 0
  | inr 1 => 3
  | inr 2 => 4
  | inr 3 => 5
  | inr n => n
  end.

Definition slot_initial (n : nat) := n == (slot_pid initial_pid).

Definition T_intermediate := Option THandlerOutput.
Definition f_proj (i : [T_intermediate]) : forall n, [Option (slot_I n)] :=
  fun n => match n with
           | 4 => i     (*the high process receives the disk-interrupt handler's output*)
           | _ => None  (*every other process receives nothing*)
           end.

(* pool p_pub p_priv p_sched =
     process_pool 5 slot_initial slot_I slot_O T_intermediate f_proj slot_pid
       (slot_procs p_pub p_priv p_sched) *)
Definition pool (runtime : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) :=
  @process_pool cur_pid 5 slot_initial slot_I (slot_O Opub Opriv) T_intermediate f_proj slot_pid
    (slot_procs runtime p_pub p_priv p_sched).


(* === 3. Stateful wrapper === *)

Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.
(*We define a stateful wrapper that will be wrapped around the process pool*)
(* reactive_system state state_update no_output p pool_input =
     map inl (inr_or_def no_output)
       (loop (map id snd
         (sta state_update (fun _ v => v) state
           (map pool_input inr (maybe p))))) *)
Definition reactive_system
  (cur_pid state_type : Ty)
  (state : [state_type])
  (T_in T_out_userview T' : Ty)
  (state_update : [Sum T_in T_out_userview] -> [state_type] -> [state_type])
  (no_output : [T_out_userview])
  (p : Proc (Times cur_pid T') T_out_userview)
  (pool_input : [Times state_type (Sum T_in T_out_userview)] -> [Option (Times cur_pid T')])
  : Proc T_in T_out_userview :=
  (@map T_in (Sum T_in T_out_userview) (Sum T_in T_out_userview) T_out_userview inl (inr_or_def no_output)
                          (@loop (Sum T_in T_out_userview)
                             (@map _ _ (Times _ _) _
                                id snd
                                (@sta _ _ state_type state_update (fun _ v => v) state
                                   (@map (Times state_type (Sum _ _ ))
                                      (Option (Times cur_pid T')) _ (Sum T_in T_out_userview) pool_input inr (maybe p)))))).


(* === 4. Model state === *)
Definition mask := Bool.
Definition pending := Bool.
Definition ir_bits := Times pending mask.
Definition ir_count := Option Nat.
Definition ic := Times ir_bits (Times ir_bits ir_bits).
Definition count := Nat.
Definition re_sched := Bool.
Definition prev_pid := Option Nat.
Definition pids := Times cur_pid prev_pid.
(* ic_count bundles the interrupt-handler time slice with the interrupt controller.
   ir_count = None  -> feature disabled
   ir_count = Some n -> n steps of handler execution left; Some 0 -> return to user space *)
Definition ic_count := Times ir_count ic.
Definition bool_state := Times re_sched ic_count.
(* The interrupt controller has one entry per external interrupt and one more,
   [nop_irq], for the NOP handler.  No external interrupt raises the NOP entry;
   the sliced policy sets it pending itself, to use the NOP handler as filler. *)
Definition irq := Option TInterrupt.
Notation timer_irq := (Some TimerInterrupt).
Notation disk_irq := (Some DiskInterrupt).
Notation nop_irq := None (only parsing).
Definition all_interrupts : seq [irq] :=
  [:: timer_irq; disk_irq; nop_irq].
Definition sans_timer : seq [irq] :=
  [:: disk_irq; nop_irq].
Definition state_type := Times pids bool_state.

Definition get_pids (v : [state_type]) := v.1.
Definition get_bool_state (v : [state_type]) := v.2.
Definition get_cur_pid (v : [state_type]) := (get_pids v).1.
Definition get_prev_pid (v : [state_type]) := (get_pids v).2.
Definition get_re_sched (v : [state_type]) := (get_bool_state v).1.
Definition get_ic_count (v : [state_type]) := (get_bool_state v).2.
Definition get_ir_count (v : [state_type]) := (get_ic_count v).1.
Definition get_ic (v : [state_type]) := (get_ic_count v).2.

Definition get_ir_bits' (ic : [ic]) (ir : [irq]) : [ir_bits] :=
  match ir with
  | nop_irq   => ic.1
  | disk_irq  => ic.2.1
  | timer_irq => ic.2.2
  end.
Definition get_ir_bits (v : [state_type]) (ir : [irq]) := get_ir_bits' (get_ic v) ir.

Definition get_pending' (bits : [ir_bits]) := bits.1.
Definition get_mask' (bits : [ir_bits]) := bits.2.

Definition get_ir_pending (v : [state_type]) (ir : [irq]) := get_pending' (get_ir_bits v ir).
Definition get_ir_mask (v : [state_type]) (ir : [irq]) := get_mask' (get_ir_bits v ir).

Definition update_pids (v : [state_type]) pids : [state_type] := (pids,v.2).
Definition update_bool_state (v : [state_type]) bs : [state_type] := (v.1,bs).
Definition update_cur_pid (v : [state_type]) cur_pid : [state_type] := update_pids v (cur_pid,(get_pids v).2).
Definition update_prev_pid (v : [state_type]) prev_pid : [state_type] := update_pids v ((get_pids v).1,prev_pid).
Definition update_re_sched (v : [state_type]) re_sched : [state_type] := update_bool_state v (re_sched,(get_bool_state v).2).

Definition update_ir_bits' (myic : [ic]) (ir : [irq]) (bits : [ir_bits]) : [ic] :=
  match ir with
  | nop_irq   => (bits, myic.2)
  | disk_irq  => (myic.1, (bits, myic.2.2))
  | timer_irq => (myic.1, (myic.2.1, bits))
  end.

Definition update_ic_count (v : [state_type]) icc : [state_type] := update_bool_state v ((get_bool_state v).1,icc).
Definition update_ir_count (v : [state_type]) c : [state_type] := update_ic_count v (c,(get_ic_count v).2).
Definition update_ic (v : [state_type]) ic : [state_type] := update_ic_count v ((get_ic_count v).1,ic).
Definition update_ir_bits (v : [state_type]) (ir : [irq]) (bits : [ir_bits]) := update_ic v (update_ir_bits' (get_ic v) ir bits).

Definition update_ir_pending (v : [state_type]) (ir : [irq]) pending : [state_type] :=
  update_ir_bits v ir (pending,get_ir_mask v ir).
Definition update_ir_mask (v : [state_type]) (ir : [irq]) mask : [state_type] :=
  update_ir_bits v ir (get_ir_pending v ir,mask).

Definition or_ir_bits (b1 b2 : [ir_bits]) : [ir_bits] := (b1.1 || b2.1, b1.2 || b2.2).
Definition or_ic (c1 c2 : [ic]) : [ic] :=
  (or_ir_bits c1.1  c2.1,
   (or_ir_bits c1.2.1 c2.2.1,
    or_ir_bits c1.2.2 c2.2.2)).
(* keep the base state's time slice (s1.2.1); only the interrupt controller is merged *)
Definition or_bool_state (s1 s2 : [bool_state]) : [bool_state] := (s1.1 || s2.1, (s1.2.1, or_ic s1.2.2 s2.2.2)).

Definition set_masks (v : [state_type]) : [state_type] :=
  foldr (fun I v' => update_ir_mask v' I true) v all_interrupts.
Definition unset_masks (v : [state_type]) : [state_type] :=
  foldr (fun I v' => update_ir_mask v' I false) v all_interrupts.
Definition unset_masks_sans (v : [state_type]) : [state_type] :=
  foldr (fun I v' => update_ir_mask v' I false) v sans_timer.
Definition unset_tI (v : [state_type]) : [state_type] := update_ir_mask v timer_irq false.
Definition set_tI (v : [state_type]) : [state_type] := update_ir_mask v timer_irq true.
Definition set_otherIs (v : [state_type]) : [state_type] := foldr (fun I v' => update_ir_mask v' I true) v sans_timer.
Definition masks_set (v : [state_type]) :=
  foldr (fun I b => (get_ir_mask v I) && b) true all_interrupts.


(* === 5. Reading the pool's output ===

   Slot accessors and the two projections that leave the pool: [no_output], the output
   emitted when no slot produced one, and [pool_input], the value fed back in.
   Both policies use all of these unchanged. *)

Definition tI_out (Opub Opriv : Ty) (o : [T_out Opub Opriv]) :=
  match o with
  | (_,(_,(_,(_,(_,x))))) => x
  end.

Definition dI_out (Opub Opriv : Ty) (o : [T_out Opub Opriv]) :=
  match o with
  | (_,(_,(_,(_,(x,_))))) => x
  end.

Definition nop_ir_out (Opub Opriv : Ty) (o : [T_out Opub Opriv]) :=
  match o with
  | (_,(_,(_,(x,(_,_))))) => x
  end.

Definition is_ir_out_done (Opub Opriv : Ty) (o : [T_out Opub Opriv]) : [Option irq] :=
  if tI_out o is Some Notify then Some timer_irq
  else if dI_out o is Some Notify then Some disk_irq
  else if nop_ir_out o is Some Notify then Some nop_irq
  else None.

Definition no_output (Opub Opriv : Ty) : [ T_out Opub Opriv ]  := (None,(None,(None,(None,(None,None))))).

(*discards input from the inner process, only allowed to affect bit in ic, not pid*)
Definition pool_input (Opub Opriv : Ty) (si : [Times state_type (Sum T_in (T_out Opub Opriv))]) : [Option (Times cur_pid T_intermediate)] :=
  if si.2 is inr o then Some (get_cur_pid si.1, dI_out o) else None.

(* The user view: keep the two user slots, erase the scheduler and all three
   handlers.  Used by [model_sliced_userview] in section 9. *)
Definition parse_output (Opub Opriv : Ty) (o : [T_out Opub Opriv]) : [T_out_userview Opub Opriv] :=
  match o with
  | (Some public,_) => Some (inl public)
  | (None,(Some prv,_)) => Some (inr prv)
  | _ => None
  end.


(* === 6. State transitions === *)

(* An event is either an arriving interrupt (inl) or a pool output (inr), and a
   stage of the transition reacts to exactly one of the two.  [step_sum f g] is
   the state update that runs [f] on an input and [g] on an output.  Composition
   is componentwise -- [step_sum f g \o step_sum f' g' = step_sum (f \o f') (g \o
   g')] pointwise in the event -- so a pipeline of stages collapses into a single
   [step_sum] whose summands are the input and output pipelines. *)
Definition step_sum (Opub Opriv : Ty)
  (f : [T_in] -> [state_type] -> [state_type])
  (g : [T_out Opub Opriv] -> [state_type] -> [state_type])
  : [Sum T_in (T_out Opub Opriv)] -> [state_type] -> [state_type] :=
  fun i v =>
  match i with
  | inl i => f i v
  | inr o => g o v
  end.

(* An arriving interrupt is recorded as pending; whether it is serviced is
   decided later, by [initiate_next].  This is the whole of the input summand:
   f_EP forbids the transition from taking any decision on an input event. *)
Definition set_pending (i : [T_in]) (v : [state_type]) : [state_type] :=
  update_ir_pending v (Some i) true.

Definition is_sched_out (Opub Opriv : Ty) (o : [T_out Opub Opriv]) :=
  match o with
  | (None,(None,(Some n,_))) => Some n
  | _ => None
  end.
Definition check_scheduler (Opub Opriv : Ty) (o : [T_out Opub Opriv]) (v : [state_type])  :=
  if is_sched_out o is Some n then update_cur_pid v (inr n) else v.

(* [check_scheduler] installs the pid a scheduler output names as the current
   one.  Note this reads the scheduler slot only -- the user slots are inspected
   for None-ness and nothing more (see [is_sched_out]), which is what keeps the
   state transition independent of what userspace does. *)

(* The pid of the handler an interrupt runs in. *)
Definition ir_handler_pid (ir : [irq]) : [cur_pid] :=
  match ir with
  | timer_irq => inr 0
  | disk_irq  => inl true
  | nop_irq   => inl false
  end.

(* It selects the slot the interrupt's own position in all_interrupts names. *)
Lemma slot_pid_ir_handler_pid : forall ir, slot_pid (ir_handler_pid ir) = index ir all_interrupts.
Proof. by case=> [[]|]. Qed.

(* before overriding cur_pid, save it to prev_pid if it is a user process *)
Definition save_cur_to_prev (v : [state_type]) : [state_type] :=
  if get_cur_pid v is inr n
  then update_prev_pid v (Some n)
  else v.

Definition initiate_handler (ir : [irq]) (v : [state_type]) :=
  update_ir_pending (set_masks (update_cur_pid (save_cur_to_prev v) (ir_handler_pid ir))) ir false.

(* a handler is selectable iff pending and not masked *)
Definition ir_ready (v : [state_type]) (ir : [irq]) : bool :=
  get_ir_pending v ir && ~~ get_ir_mask v ir.

Definition first_ready (v : [state_type]) : option [irq] :=
  ohead [seq ir <-  all_interrupts | (ir_ready v ir) ].

Definition is_handler_pid (v : [state_type]) :=
    match get_cur_pid v with
    | inr 0 => true
    | inr _ => false
    | _ => true
    end.

Definition scheduler_pid : [cur_pid] := inr 1.

Definition initiate_scheduler  (v : [state_type]) := update_re_sched (update_prev_pid (update_cur_pid v scheduler_pid) None) false.

Definition get_prev_pid_wrap (v : [state_type]) : [Option cur_pid] := if get_prev_pid v is Some n then Some (inr n) else None.
Definition initiate_prev_pid  (v : [state_type]) := update_prev_pid (update_cur_pid v (odflt scheduler_pid (get_prev_pid_wrap v))) None.

Definition initiate_next (restore_invariant :  [state_type] -> [state_type]) :  [state_type] -> [state_type] :=
  fun v => if (masks_set v) then v (*handler running*) else
             let v := restore_invariant v (*apply time slice logic to bools*) in
             if first_ready v is Some ir then initiate_handler ir v (*first or later handler in the time slice is initiated here; inside a slice the NOP handler is always pending, so one runs*) else
               if is_handler_pid v then if get_re_sched v then initiate_scheduler v else initiate_prev_pid v  (*mask not set but we are in handler pid, we have just finished the time slice*) else
                 v (*we are running in user space*).



(* The state transition.  An arriving interrupt only records itself; everything
   it eventually causes happens in the output summand, where the input is no
   longer the thing being varied.  That split is forced by f_EP, which under
   eqsum_L constrains the input summand alone. *)
Definition state_step (Opub Opriv : Ty) (service_policy : [T_out Opub Opriv] -> [state_type] -> [state_type]) (restore_invariant : [state_type] -> [state_type]) : [Sum T_in (T_out Opub Opriv)] -> [state_type] -> [state_type] :=
  step_sum set_pending
           (fun o => (initiate_next restore_invariant) \o (service_policy o) \o (@check_scheduler Opub Opriv o)).


(* === 7. The generic model ===

   Everything above is shared.  A model is the process pool run inside the
   stateful wrapper, and the only freedom left is the triple

     (init_policy, service_policy, restore_invariant)

   that section 8 fixes in two different ways.  The first two decide when a
   handler may run and together form the *interrupt policy*; the [_policy]
   suffix marks them.  [restore_invariant] is not part of it: it only helps the
   proof, and never changes a reachable state (restore_invariant_noop).  Note [runs] is not a parameter
   here: the slice size reaches the model only through [service_policy],
   already applied. *)
Definition model (runtime : nat) (Opub Opriv : Ty)
  (init_policy : [state_type])
  (service_policy : [T_out Opub Opriv] -> [state_type] -> [state_type])
  (restore_invariant : [state_type] -> [state_type])
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out Opub Opriv) :=
  @reactive_system cur_pid state_type init_policy T_in (T_out Opub Opriv) T_intermediate
    (state_step service_policy restore_invariant) (no_output Opub Opriv)
    (pool runtime p_pub p_priv p_sched) (@pool_input Opub Opriv).


(* #################################################################
   PART II -- the two interrupt policies
   ################################################################# *)

(* === 8. model_immediate and model_sliced, side by side ===

   The two policies are the same [model] at two different triples, and that
   difference is the whole security story:

     parameter            model_immediate            model_sliced
     -----------------------------------------------------------------------
     init_policy          immediate_init             sliced_init
                          no slice, no masks set     slice at [Some 0], every
                                                     mask but the timer's set
     service_policy       immediate_service          sliced_service runtime runs
                          a finished handler         a finished timer handler opens
                          unmasks everything, so     a slice and requests a
                          a pending interrupt is     reschedule; each handler
                          serviced at once           boundary inside it reopens the
                                                     masks and queues a NOP run; the
                                                     slice is counted down and
                                                     closed on a handler boundary
     restore_invariant    id                         restore_invariant
                          nothing                    re-imposes the slice invariant
                                                     for the proof; the identity on
                                                     every reachable state
                                                     (restore_invariant_noop)

   In [model_immediate] a secret interrupt is therefore serviced the moment it
   arrives, displacing whatever was running; in [model_sliced] it can only be
   serviced inside a slice, where it replaces a NOP handler run of the same
   length. *)

(* -- model_immediate -- *)

Definition false_ir_bits : [ir_bits] := (false,false).
Definition false_ic : [ic] := ((false,false),(false_ir_bits,false_ir_bits)).
Definition immediate_init : [state_type] := ((initial_pid,None),(false,(None,false_ic))).

Definition immediate_service (Opub Opriv : Ty) (o : [T_out Opub Opriv]) (v : [state_type])  :=
  if is_ir_out_done o is Some ir then let v := unset_masks v in if ir is timer_irq then update_re_sched v true else v else v.

(* model_immediate p_pub p_priv p_sched =
     model immediate_init immediate_service id p_pub p_priv p_sched *)
Definition model_immediate (runtime : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out Opub Opriv) :=
  model runtime immediate_init (@immediate_service Opub Opriv) id
    p_pub p_priv p_sched.

(* -- model_sliced -- *)

Definition mask_most : [ic] := ((false,true),((false,true),(false,false))). (*mask set for everything but timer interrupt*)

Definition sliced_init : [state_type] := ((initial_pid,None),(false,(Some 0,mask_most))).

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

(* The timer handler's completion opens a slice and, as in [model_immediate],
   requests a reschedule for when control next leaves the handlers. *)
Definition initiate_ir (runtime runs : nat) (Opub Opriv : Ty) (o : [T_out Opub Opriv]) (v : [state_type]) : [state_type] :=
  if tI_out o is Some Notify
  then update_re_sched (update_ir_count v (Some (time_slice runtime runs))) true else v.

(* At each handler boundary inside a slice: reopen the disk and NOP masks, keep
   the timer masked, and make the NOP handler pending, so that the next handler
   run happens whether or not a disk interrupt is waiting.  This is the filler. *)
Definition check_handler_completed (runtime : nat) (v : [state_type]) : [state_type] :=
  if handler_completed runtime (get_ir_count v)
  then update_ir_pending (set_tI (unset_masks v)) nop_irq true else v.

Definition check_ir_count (v : [state_type]) : [state_type] :=
    match (get_ir_count v) with
    | Some n.+1 => update_ir_count v (Some n)
    | Some 0 => update_ir_count (set_otherIs (unset_tI v)) None
    | None => v
    end.

Definition timeslice_live (c : [ir_count]) := match c with | Some n => 0 < n | _ => false end.

(* restore_invariant writes the time-slice invariant into the state just before
   [initiate_next] chooses: inside a slice the NOP handler is pending and the
   timer masked, outside it the disk and NOP handlers are masked, and the NOP
   mask equals the disk mask.  The sliced policy already maintains all of this, so on
   every reachable state it changes nothing (restore_invariant_noop, below).  It
   exists for the proof: stated unconditionally, it lets the [fv_NI] argument
   for [initiate_next] use the invariant without carrying reachability, and so
   conclude that if one of two related states has the disk or NOP handler ready,
   so does the other. *)

Definition restore_invariant v := let b := timeslice_live (get_ir_count v) in
                            let ic := (false,(None,((b,~~b),((false,~~b),(false,b))))) in
                            let v := update_bool_state v (or_bool_state (get_bool_state v) ic) in
                            let m := get_ir_mask v disk_irq in
                            update_ir_mask v nop_irq m.

Definition sliced_service (runtime runs : nat) (Opub Opriv : Ty) (o : [T_out Opub Opriv]) : [state_type] -> [state_type] := check_ir_count \o check_handler_completed runtime \o (initiate_ir runtime runs o). (*\o (unset_handler_masks o)*)

(* model_sliced p_pub p_priv p_sched =
     model sliced_init (sliced_service runtime runs) restore_invariant
       p_pub p_priv p_sched *)
Definition model_sliced (runtime runs : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out Opub Opriv) :=
  model runtime sliced_init (@sliced_service runtime runs Opub Opriv) restore_invariant
    p_pub p_priv p_sched.


(* -- restore_invariant is the identity wherever it is applied --

   [restore_invariant] is stated unconditionally so that the compositional proof
   of [fv_NI] can rely on the time-slice invariant without carrying reachability.
   The sliced policy itself establishes that invariant: [check_handler_completed] queues
   the NOP handler at each boundary, and [initiate_ir] requests a reschedule when
   a slice opens.  So on every state [initiate_next] actually reaches,
   [restore_invariant] changes nothing (restore_invariant_noop).

   The statement quantifies over arbitrary event sequences, not only those a
   process pool can produce, so it needs no reasoning about processes.  It needs
   [runtime != 1]: with one-step handlers the last inner boundary ticks the
   counter to [Some 0], the slice already reads as over, and restore_invariant
   masks the handler that boundary had just enabled. *)

Section SlicedInvariant.
Variables (runtime runs : nat) (Opub Opriv : Ty).
Hypothesis runtime_ne1 : runtime != 1.

(* Between steps: the NOP and disk masks agree; outside a slice they are set;
   inside a slice a handler is running. *)
Definition sliced_inv (v : [state_type]) : bool :=
  (get_ir_mask v nop_irq == get_ir_mask v disk_irq) &&
  (if timeslice_live (get_ir_count v) then masks_set v
   else get_ir_mask v disk_irq).

(* The state [initiate_next] makes its choice from. *)
Definition choice_state (o : [T_out Opub Opriv]) v :=
  sliced_service runtime runs o (check_scheduler o v).

(* At that point: as [sliced_inv], except that at a handler boundary inside a
   slice the masks are open and the NOP handler is pending. *)
Definition choice_inv (w : [state_type]) : bool :=
  (get_ir_mask w nop_irq == get_ir_mask w disk_irq) &&
  (if timeslice_live (get_ir_count w)
   then masks_set w || [&& get_ir_pending w nop_irq,
                          get_ir_mask w timer_irq,
                          ~~ get_ir_mask w disk_irq &
                          ~~ get_ir_mask w nop_irq]
   else get_ir_mask w disk_irq).

Lemma masks_setE v : masks_set v =
  [&& get_ir_mask v timer_irq, get_ir_mask v disk_irq & get_ir_mask v nop_irq].
Proof. by rewrite /masks_set /= andbT. Qed.

(* One lemma per stage of [choice_state], stated on the fields the invariant reads. *)
Lemma check_scheduler_bits (o : [T_out Opub Opriv]) v :
  [/\ get_ir_count (check_scheduler o v) = get_ir_count v,
      forall ir, get_ir_mask (check_scheduler o v) ir = get_ir_mask v ir &
      forall ir, get_ir_pending (check_scheduler o v) ir = get_ir_pending v ir].
Proof. rewrite /check_scheduler. by case: (is_sched_out o). Qed.

Lemma initiate_ir_mask (o : [T_out Opub Opriv]) v ir :
  get_ir_mask (initiate_ir runtime runs o v) ir = get_ir_mask v ir.
Proof. by rewrite /initiate_ir; case: (tI_out o) => [[|]|]. Qed.

Lemma initiate_ir_count (o : [T_out Opub Opriv]) v :
  get_ir_count (initiate_ir runtime runs o v) =
  if tI_out o is Some Notify then Some (time_slice runtime runs) else get_ir_count v.
Proof. by rewrite /initiate_ir; case: (tI_out o) => [[|]|]. Qed.

Lemma chc_count v : get_ir_count (check_handler_completed runtime v) = get_ir_count v.
Proof. rewrite /check_handler_completed. by case: (handler_completed _ _). Qed.

Lemma chc_id v : handler_completed runtime (get_ir_count v) = false ->
  check_handler_completed runtime v = v.
Proof. by rewrite /check_handler_completed => ->. Qed.

Lemma chc_bits v : handler_completed runtime (get_ir_count v) ->
  [/\ get_ir_mask (check_handler_completed runtime v) nop_irq = false,
      get_ir_mask (check_handler_completed runtime v) disk_irq = false,
      get_ir_mask (check_handler_completed runtime v) timer_irq = true &
      get_ir_pending (check_handler_completed runtime v) nop_irq = true].
Proof. rewrite /check_handler_completed => ->. by move: v => [[? ?] [? [? [[? ?] [[? ?] [? ?]]]]]]. Qed.

Lemma cic_tick v n : get_ir_count v = Some n.+1 ->
  [/\ get_ir_count (check_ir_count v) = Some n,
      forall ir, get_ir_mask (check_ir_count v) ir = get_ir_mask v ir &
      forall ir, get_ir_pending (check_ir_count v) ir = get_ir_pending v ir].
Proof. rewrite /check_ir_count => ->. by split => // -[]. Qed.

Lemma cic_close v : get_ir_count v = Some 0 ->
  [/\ get_ir_count (check_ir_count v) = None,
      get_ir_mask (check_ir_count v) nop_irq = true &
      get_ir_mask (check_ir_count v) disk_irq = true].
Proof. rewrite /check_ir_count => ->. by move: v => [[? ?] [? [? [[? ?] [[? ?] [? ?]]]]]]. Qed.

Lemma cic_none v : get_ir_count v = None -> check_ir_count v = v.
Proof. by rewrite /check_ir_count => ->. Qed.

(* Opening a slice lands on a boundary, and every boundary is at least 2. *)
Lemma hc_slice : time_slice runtime runs != 0 ->
  handler_completed runtime (Some (time_slice runtime runs)).
Proof. by move=> H; rewrite /handler_completed H /time_slice modnMl. Qed.

Lemma hc_ge2 m : handler_completed runtime (Some m) -> (2 <= m)%N.
Proof.
rewrite /handler_completed => /andP [Hm Hd].
case: runtime runtime_ne1 Hd => [|[|r]] // _.
- by rewrite modn0 (negbTE Hm).
- move=> Hd. have Hdv : (r.+2 %| m)%N by [].
  apply: leq_trans (dvdn_leq _ Hdv) => //. by rewrite lt0n.
Qed.

Lemma choice_inv_step (o : [T_out Opub Opriv]) v : sliced_inv v -> choice_inv (choice_state o v).
Proof.
move=> Hv.
have -> : choice_state o v =
          check_ir_count (check_handler_completed runtime (initiate_ir runtime runs o (check_scheduler o v))) by [].
case: (check_scheduler_bits o v) => Cc Cm Cp.
set v1 := initiate_ir runtime runs o (check_scheduler o v).
have M1 : forall ir, get_ir_mask v1 ir = get_ir_mask v ir by move=> ir; rewrite initiate_ir_mask Cm.
have C1 : get_ir_count v1 = if tI_out o is Some Notify then Some (time_slice runtime runs) else get_ir_count v
  by rewrite initiate_ir_count Cc.
move: Hv; rewrite /sliced_inv /choice_inv masks_setE => /andP [/eqP Hdk Hl].
case HC: (handler_completed runtime (get_ir_count v1)).
- (* a boundary: masks open, NOP pending, and the slice is still live *)
  case: (chc_bits HC) => Bd Bk Bt Bp.
  move: HC; case E1: (get_ir_count v1) => [m|] // HC.
  have Hm := hc_ge2 HC.
  case: m Hm E1 HC => [|[|k]] // _ E1 _.
  have E2 : get_ir_count (check_handler_completed runtime v1) = Some k.+2 by rewrite chc_count.
  case: (cic_tick E2) => -> Tm Tp.
  by rewrite /timeslice_live masks_setE !Tm !Tp Bd Bk Bt Bp.
- rewrite (chc_id HC).
  case E1: (get_ir_count v1) => [[|[|k]]|].
  + by case: (cic_close E1) => -> -> ->.
  + case: (cic_tick E1) => -> Tm Tp.
    rewrite /timeslice_live !Tm !M1 Hdk eqxx.
    move: C1 Hl; rewrite E1.
    case: (tI_out o) => [[|]|].
    * by move<-; rewrite /timeslice_live masks_setE => /and3P [].
    * case=> /esym /eqP; rewrite /time_slice muln_eq1 => /andP [_ /eqP r1].
      by move: runtime_ne1; rewrite r1.
    * by move<-; rewrite /timeslice_live masks_setE => /and3P [].
  + case: (cic_tick E1) => -> Tm Tp.
    rewrite /timeslice_live !Tm !M1 Hdk eqxx /=.
    move: C1 Hl HC; rewrite E1.
    case: (tI_out o) => [[|]|].
    * move<- => Hl _; rewrite masks_setE !Tm !M1.
      by move: Hl => /= ->.
    * case=> Hs Hl; rewrite Hs hc_slice //; by rewrite -Hs.
    * move<- => Hl _; rewrite masks_setE !Tm !M1.
      by move: Hl => /= ->.
  + rewrite (cic_none E1) E1 !M1 Hdk eqxx /=.
    move: C1 Hl; rewrite E1.
    by case: (tI_out o) => [[|]|] // <-.
Qed.

Lemma restore_invariant_id w : choice_inv w -> ~~ masks_set w -> restore_invariant w = w.
Proof.
move: w => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]].
case: c => [[|n]|]; move: rs dp dm kp km tp tm => [] [] [] [] [] [] [];
  vm_compute; intros; solve [discriminate | reflexivity].
Qed.

Lemma sliced_inv_step (e : [Sum T_in (T_out Opub Opriv)]) v :
  sliced_inv v ->
  sliced_inv (state_step (@sliced_service runtime runs Opub Opriv) restore_invariant e v).
Proof.
case: e => [i|o] Hv.
- move: v Hv => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]] Hv.
  by case: i.
- have -> : state_step (@sliced_service runtime runs Opub Opriv) restore_invariant (inr o) v =
            initiate_next restore_invariant (choice_state o v) by [].
  have := choice_inv_step o Hv; move: (choice_state o v) => w Hw.
  rewrite /initiate_next.
  case Ms: (masks_set w).
  + move: Hw; rewrite /choice_inv /sliced_inv Ms => /andP [-> H].
    by case: (timeslice_live _) H.
  + rewrite restore_invariant_id //; last by rewrite Ms.
    case FR: (first_ready w) => [ir|].
    * move: w {Hw Ms FR} => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]].
      by case: ir => [[]|]; case: cur => [b|m]; case: c => [[|n]|].
    * have NL : ~~ timeslice_live (get_ir_count w).
        apply/negP => L; move: Hw FR; rewrite /choice_inv L Ms /= => /andP [_ /and4P [Hp _ _ Hdm]].
        have Rd : ir_ready w nop_irq by rewrite /ir_ready Hp Hdm.
        rewrite /first_ready /=.
        by case: (ir_ready w timer_irq); case: (ir_ready w disk_irq); rewrite ?Rd.
      have Hinv : sliced_inv w by move: Hw; rewrite /choice_inv /sliced_inv (negbTE NL).
      move: w Hinv {Hw Ms FR NL} => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]] Hinv.
      by case: (is_handler_pid _); first case: (get_re_sched _).
Qed.

(* The state after any sequence of events, starting from [sliced_init]. *)
Definition sliced_run (es : seq [Sum T_in (T_out Opub Opriv)]) :=
  foldl (fun v e => state_step (@sliced_service runtime runs Opub Opriv) restore_invariant e v)
        sliced_init es.

Lemma sliced_run_inv es : sliced_inv (sliced_run es).
Proof.
rewrite /sliced_run; elim/last_ind: es => [|es e IH] //.
by rewrite foldl_rcons; apply: sliced_inv_step.
Qed.

Theorem restore_invariant_noop es o :
  ~~ masks_set (choice_state o (sliced_run es)) ->
  restore_invariant (choice_state o (sliced_run es)) = choice_state o (sliced_run es).
Proof. by apply: restore_invariant_id; apply: choice_inv_step; apply: sliced_run_inv. Qed.

End SlicedInvariant.


(* === 9. model_sliced_userview === *)

Definition model_sliced_userview (runtime runs : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out_userview Opub Opriv) :=
  map id (@parse_output Opub Opriv) (model_sliced runtime runs p_pub p_priv p_sched).

Definition out_equiv_userview (Opub Opriv : Ty) : cEquiv [T_out_userview Opub Opriv] := eqmaybe_nobody (eqsum (public_equiv Opub) (private_equiv Opriv)).


(* #################################################################
   PART III -- one concrete system
   ################################################################# *)

(* === 10. A concrete system ===

   Nothing in Parts I and II names a user process, a scheduler, a handler
   length or a slice size.  This section supplies one of each, so that the
   models can be run and their behaviour exhibited as traces. *)

(* p_pub_concrete = out GetRequest *)
Definition p_pub_concrete := @out Empty TPublicOutput GetRequest.


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
(* p_priv_concrete = alternate Syscall NOP tt (fun i => i == Notify) *)
Definition p_priv_concrete := @alternate THandlerOutput TTypeSyscall Unit Syscall Idle tt (fun i => i == Notify).

(* scheduler =
     map id (fun o => o.1 + 2)
       (sta (fun _ v => v) (fun _ v => v.+1 %% 2) 1 (out tt)) *)
Definition scheduler : Proc Empty Nat :=
  map (O := Times Nat Unit) (O' := Nat) id
    (fun o => o.1 + 2)                        (*skip the interrupt handlers to reach p_priv_concrete and p_pub_concrete*)
    (sta (V := Nat) (O := Unit)
       (fun _ v => v) (fun _ v => v.+1 %% 2)
       1                                      (*will start scheduling the high process*)
       (out (O := Unit) tt)).

(* The concrete handler length and slice: handlers two output steps long, a
   slice of two handler runs. *)
Definition handler_runtime := 2.
Definition slice_runs := 2.

Definition slot_procs_concrete := slot_procs handler_runtime p_pub_concrete p_priv_concrete scheduler.
Definition pool_concrete := pool handler_runtime p_pub_concrete p_priv_concrete scheduler.

Definition model_immediate_concrete := model_immediate handler_runtime p_pub_concrete p_priv_concrete scheduler.
Definition model_sliced_concrete := model_sliced handler_runtime slice_runs p_pub_concrete p_priv_concrete scheduler.
Definition model_sliced_userview_concrete :=
  model_sliced_userview handler_runtime slice_runs p_pub_concrete p_priv_concrete scheduler.

(* Sanity, at this instance: the computed test agrees with the enumeration
   [Some 2 | Some 4] it replaced, on every value the counter can reach (the
   counter starts at [time_slice] and is decremented to [Some 0] before being
   cleared). *)
Lemma handler_completed_reachable n :
  n <= time_slice handler_runtime slice_runs ->
  handler_completed handler_runtime (Some n) = ((n == 2) || (n == 4)).
Proof. by case: n => [|[|[|[|[|n]]]]]. Qed.


(* === 11. Example traces ===

   Each model is exercised on two runs of the concrete system, on the same input
   schedule: one with no disk interrupt and one with a disk interrupt.  Reading
   the two [model_immediate] traces against each other shows the leak -- the
   public process loses output steps to the handler -- and the two
   [model_sliced] traces show that it is gone.  The [model_sliced_userview]
   traces are the [model_sliced] ones under [parse_output]. *)

(* -- Named inputs and outputs -- *)
Definition Tsum' := ([T_in] + [T_outC])%type.
Definition Tsum := Sum T_in T_out_userviewC.

Definition dI' : Tsum' := inl DiskInterrupt.
Definition tI' : Tsum' := inl TimerInterrupt.
Definition low_out x : [T_outC] := (Some x,(None,(None,(None,(None,None))))).
Definition high_out x : [T_outC] := (None,(Some x,(None,(None,(None,None))))).
Definition sched_o x : [T_outC] := (None,(None,(Some x,(None,(None,None))))).
Definition nop_o x : [T_outC] := (None,(None,(None,(Some x,(None,None))))).
Definition dI_o x : [T_outC] := (None,(None,(None,(None,(Some x,None))))).
Definition tI_o x : [T_outC] := (None,(None,(None,(None,(None,Some x))))).

Definition tmr_done' : Tsum' :=  inr (tI_o (Notify)).
Definition tmr_step' : Tsum' :=  inr (tI_o (Nothing)).

Definition dsk_done' : Tsum' :=  inr (dI_o (Notify)).
Definition dsk_step' : Tsum' :=  inr (dI_o (Nothing)).

Definition out_get' : Tsum' := inr (low_out GetRequest).
Definition out_nop' : Tsum' := inr (high_out Idle).
Definition out_syscall' : Tsum' := inr (high_out Syscall).

Definition sched_pub' : Tsum' := inr (sched_o 3).
Definition sched_priv' : Tsum' := inr (sched_o 2).

Definition nop_step' : Tsum' :=  inr (nop_o (Nothing)).
Definition nop_done' : Tsum' :=  inr (nop_o (Notify)).

Definition out_get : [Tsum] := inr (Some (inl (GetRequest))).
Definition out_nop : [Tsum] := inr (Some (inr Idle)).
Definition out_syscall : [Tsum] := inr (Some (inr Syscall)).
Definition w_None : [Tsum] := inr None.
Definition tI : [Tsum] := inl TimerInterrupt.
Definition dI : [Tsum] := inl DiskInterrupt.

Definition seqtype' := seq Tsum'.
Definition seqtype := seq ([T_in] + [T_out_userviewC]).


(* -- the four runs --

   All four share one input schedule: the disk interrupt (if any) after step 1,
   the timer interrupt after step 3; each has twelve output steps.  Without the
   disk interrupt the two policies behave alike.  With it, model_immediate hands
   steps 3-4 to the disk handler, taking them from the public process, while
   model_sliced records the interrupt as pending and runs the disk handler in
   place of the first NOP run of the slice.  Each "with" run minus its [dI'] is
   the matching "no" run, so each pair is an instance of the deletion clause of
   NI. *)
Definition immediate_no_dI' : seqtype' := [::out_get';out_get';out_get';tI';out_get';tmr_step';tmr_done';sched_priv';out_nop';out_nop';out_nop';out_nop';out_nop'].
Definition immediate_with_dI' : seqtype' := [::out_get';dI';out_get';dsk_step';tI';dsk_done';tmr_step';tmr_done';sched_priv';out_syscall';out_nop';out_nop';out_nop';out_nop'].
Definition sliced_no_dI' : seqtype' := [::out_get';out_get';out_get';tI';out_get';tmr_step';tmr_done';nop_step';nop_done';nop_step';nop_done';sched_priv';out_nop'].
Definition sliced_with_dI' : seqtype' := [::out_get';dI';out_get';out_get';tI';out_get';tmr_step';tmr_done';dsk_step';dsk_done';nop_step';nop_done';sched_priv';out_syscall'].

Ltac rewr := rewrite /model_immediate_concrete /model_immediate /model /reactive_system /pool_concrete /pool /process_pool /slot_initial /p_pub_concrete /alternate /p_priv_concrete /pool_input /tI_o /ir_handler /f_proj /scheduler /low_out /model_sliced_concrete /model_sliced /pool_concrete /pool /pool_input /f_proj.

Ltac lsolv := try solve [ reduce_tac;reduce_tac | reduce_tac;try solve [reduce_once | econ];simpl;first (reduce_tac;reduce_tac)];simpl.
Ltac reduce_tac2 :=
  (try rewr);
   (repeat
      reduce_once);(try swi_instans); rewrite ?eqxx /= /xor /=.

Ltac sta_state_reduce :=
  match goal with
  | |- context [(@sta (Sum T_in T_outC) (Sum T_in T_outC) state_type (state_step _ _) _ ?state _)] =>let reduced := eval cbv in state in
                                                                                                          pattern state; match goal with |- ?F state => change (F reduced) end; cbv beta
  end.

Ltac trace_step := (first [econ;[idtac | econ | idtac] | econ];
  reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).
(* the last element is proved by hand, to avoid evar holes in the proof *)
Ltac trace_last := (first [econ;[idtac | econ | idtac] | econ];
  reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans);
  econ; reduce_tac2;reduce_tac2; econ; econ; reduce_tac; econ; econ;
  reduce_tac; econ; econ; reduce_tac; econ; econ; reduce_tac; econ;
  econ; reduce_tac; econ; econ; reduce_tac; econ.

Lemma trace_immediate_no_dI' l : Trace (public_equiv _) l immediate_no_dI' model_immediate_concrete.
Proof. rewr;simpl;rewr;simpl;rewr;simpl;rewr. sta_state_reduce. do 12 trace_step. trace_last. Qed.

Lemma trace_immediate_with_dI' l : Trace (public_equiv _) l immediate_with_dI' model_immediate_concrete.
Proof. rewr;simpl;rewr;simpl;rewr;simpl;rewr. do 13 trace_step. trace_last. Qed.

Lemma trace_sliced_no_dI' l : Trace (public_equiv _) l sliced_no_dI' model_sliced_concrete.
Proof. rewr;simpl;rewr;simpl;rewr;simpl;rewr. do 12 trace_step. trace_last. Qed.

Lemma trace_sliced_with_dI' l : Trace (public_equiv _) l sliced_with_dI' model_sliced_concrete.
Proof. rewr;simpl;rewr;simpl;rewr;simpl;rewr. do 13 trace_step. trace_last. Qed.


(* -- model_sliced_userview traces -- *)

Definition map_tr (I O O' : Ty) (f : [O] -> [O']) (s : seq ([I] + [O])) := seq.map (fun x => match x with | inl x' => inl x' | inr y => inr (f y) end) s.
Lemma Trace_map : forall (A B B' : Ty) (p : Proc A B) (f : [B] -> [B']) (s : seq ([A] + [B])) (BRel : cEquiv [B]) (BRel' : cEquiv [B']) l,
    f_NI BRel BRel' f ->
    Trace BRel l s p -> Trace BRel' l (map_tr f s) (map id f p).
Proof.
  intros.
  elim : H0;ssa.
  econ. econ. econ. eauto. done.
  econ. econ. econ. eauto. apply H. done. done.
Qed.


Definition good_no_dI : seqtype := [::out_get;out_get;out_get;tI;out_get;w_None;w_None;w_None;w_None;w_None;w_None;w_None;out_nop].
Definition good_with_dI : seqtype := [::out_get;dI;out_get;out_get;tI;out_get;w_None;w_None;w_None;w_None;w_None;w_None;w_None;out_syscall].

Lemma good_no_dI_eq : map_tr (@parse_output TPublicOutput TTypeSyscall) sliced_no_dI' = good_no_dI.
Proof. ssa. Qed.

Lemma good_with_dI_eq : map_tr (@parse_output TPublicOutput TTypeSyscall) sliced_with_dI' = good_with_dI.
Proof. ssa. Qed.

Lemma trace_no_dI : forall l, Trace (public_equiv _) l good_no_dI model_sliced_userview_concrete.
Proof.
  intros. rewrite -good_no_dI_eq. eapply Trace_map.
  2:eapply trace_sliced_no_dI'.
  mrw. ssa. subst. done.
Qed.

Lemma trace_with_dI : forall l, Trace (public_equiv _) l good_with_dI model_sliced_userview_concrete.
Proof.
  intros. rewrite -good_with_dI_eq. eapply Trace_map.
  2:eapply trace_sliced_with_dI'.
  mrw. ssa. subst. done.
Qed.

