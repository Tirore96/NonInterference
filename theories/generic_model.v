
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
   The generic process-scheduling model: everything the two interrupt policies
   share, ending in [model].  Nothing here is specific to a policy or to a
   concrete system.  The rest of the development builds on it:

     concrete_system.v  one choice of user processes, scheduler and handler
                        length, and the machinery for running a model on them
     model_immediate.v  [model] at the immediate policy: interrupts an attacker
                        should not know about leak through scheduling
     model_sliced.v     [model] at the sliced policy: secret interrupts are
                        received without leaking.  [model_sliced] shows every
                        pool output; [model_sliced_userview] erases all but the
                        two user slots.  Both are proved non-interfering in
                        noninterference.v

   Contents:
     0.  Input and output types
     1.  Interrupt handler and the slot family
     2.  Process pool
     3.  Stateful wrapper
     4.  Model state
     5.  Reading the pool's output
     6.  State transitions
     7.  The generic model
     8.  The two policies, side by side
   ================================================================= *)

(* A note on notation.  Processes have type [Proc I O] where I and O range over
   the inductive [Ty], and [ [t] ] denotes the Coq type that
   [t : Ty] encodes.  Indexing by [Ty] rather than by Coq's [Set] is what makes
   reductions invertible in the proofs, but it also forces the explicit [@] and
   [Ty] annotations below.  To keep the constructions readable, each process
   definition is preceded by a comment giving the same term with those
   annotations erased. *)


(* === 0. Input and output types === *)

Fixpoint times_n n (f : nat -> Ty) : Ty :=
  let t := f n in
  match n with
  | 0 => t
  | S n' => Times t (times_n n' f)
  end.
Definition times_on (n : nat) (f : nat -> Ty) := times_n n (Option \o f).


(* An interrupt is a sum: the public timer interrupt on the inl side, the
   secret disk interrupt on the inr side, the side [eqsum_R] hides.  The
   interrupt controller is indexed by the same type (irq, below). *)
Definition T_in := Sum Unit Unit.
(* A handler's output is a bool: [Notify] when its run completes, [Nothing]
   on every other step. *)
Notation Notify := true (only parsing).
Notation Nothing := false (only parsing).
(* [Opub] and [Opriv] are the alphabets of the public and the secret user
   process.  They are parameters throughout: the mechanism never inspects a
   user-slot value, only whether the slot produced one, so nothing below
   depends on what fills these two positions. *)
Definition T_out (Opub Opriv : Ty) := Times (Option Opub) (Times (Option Opriv) (Times (Option Bool) (times_on 2 (fun _ => Bool)))).
Definition T_out_userview (Opub Opriv : Ty) := Option (Sum Opub Opriv).



(* === 1. Interrupt handler and the slot family === *)

Definition handler_type := Proc Empty Bool.

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
  map (O := Times Nat Unit) (O' := Bool) id
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
  | 4 => Bool (*high*)
  | 5 => Empty (*low*)
  | _ => Empty (*padding*)
  end.

Definition slot_O (Opub Opriv : Ty) (n : nat) :=
  match n with
  | 0 => Bool (*tI*)
  | 1 => Bool (*dI*)
  | 2 => Bool (*NOP handler*)
  | 3 => Bool (*scheduler: which user runs next, see user_pid*)
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
  (p_priv : Proc Bool Opriv)  (*secret user process, slot 4*)
  (p_sched : Proc Empty Bool)            (*scheduler,           slot 3*)
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

Definition T_intermediate := Option Bool.
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
  (p_priv : Proc Bool Opriv)
  (p_sched : Proc Empty Bool) :=
  @process_pool cur_pid 5 slot_initial slot_I (slot_O Opub Opriv) T_intermediate f_proj slot_pid
    (slot_procs runtime p_pub p_priv p_sched).


(* === 3. Stateful wrapper === *)

Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.
(*We define a stateful wrapper that will be wrapped around the process pool*)
(* reactive_system state input_update output_update no_output p pool_input =
     map inl (inr_or_def no_output)
       (loop (map id (fun x => inr x.2)
         (sta input_update output_update state
           (map pool_input id (maybe p))))) *)
Definition reactive_system
  (cur_pid state_type : Ty)
  (state : [state_type])
  (T_in T_out_userview T' : Ty)
  (input_update : [Sum T_in T_out_userview] -> [state_type] -> [state_type])
  (output_update : [T_out_userview] -> [state_type] -> [state_type])
  (no_output : [T_out_userview])
  (p : Proc (Times cur_pid T') T_out_userview)
  (pool_input : [Times state_type (Sum T_in T_out_userview)] -> [Option (Times cur_pid T')])
  : Proc T_in T_out_userview :=
  (@map T_in (Sum T_in T_out_userview) (Sum T_in T_out_userview) T_out_userview inl (inr_or_def no_output)
                          (@loop (Sum T_in T_out_userview)
                             (@map (Sum T_in T_out_userview) (Sum T_in T_out_userview) (Times state_type T_out_userview) (Sum T_in T_out_userview)
                                id (fun x => inr x.2)
                                (@sta _ T_out_userview state_type input_update output_update state
                                   (@map (Times state_type (Sum _ _ ))
                                      (Option (Times cur_pid T')) _ T_out_userview pool_input id (maybe p)))))).


(* === 4. Model state === *)
Definition mask := Bool.
Definition pending := Bool.
Definition ir_bits := Times pending mask.
Definition slice_count := Nat.
Definition ic := Times ir_bits (Times ir_bits ir_bits).
Definition count := Nat.
Definition re_sched := Bool.
(* The previous pid only ever names a user process, so it is the bit
   [user_pid] reads (section 6): which user runs when the handlers are done. *)
Definition prev_pid := Bool.
Definition pids := Times cur_pid prev_pid.
(* ic_count bundles the interrupt-handler time slice with the interrupt controller.
   The slice counter is the number of output steps until the slice closes:
   0 -> no slice; 1 -> the slice's last step; n.+2 -> n.+1 steps of handler runs left. *)
Definition ic_count := Times slice_count ic.
Definition bool_state := Times re_sched ic_count.
(* The interrupt controller has one entry per external interrupt and one more,
   [nop_irq], for the NOP handler.  No external interrupt raises the NOP entry;
   the sliced policy sets it pending itself, to use the NOP handler as filler. *)
Definition irq := Option T_in.
Notation timer_irq := (Some (inl tt)).
Notation disk_irq := (Some (inr tt)).
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
Definition get_slice_count (v : [state_type]) := (get_ic_count v).1.
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
Definition update_slice_count (v : [state_type]) c : [state_type] := update_ic_count v (c,(get_ic_count v).2).
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
   handlers.  Used by [model_sliced_userview] in model_sliced.v. *)
Definition parse_output (Opub Opriv : Ty) (o : [T_out Opub Opriv]) : [T_out_userview Opub Opriv] :=
  match o with
  | (Some public,_) => Some (inl public)
  | (None,(Some prv,_)) => Some (inr prv)
  | _ => None
  end.


(* === 6. State transitions === *)

(* An arriving interrupt is recorded as pending; whether it is serviced is
   decided later, by [initiate_next].  This is the whole of the input update:
   f_EP forbids the transition from taking any decision on an input event. *)
Definition set_pending (i : [T_in]) (v : [state_type]) : [state_type] :=
  update_ir_pending v (Some i) true.

(* The [sta]'s input update.  Its input type is the loop's sum, so it also sees
   each output fed back by the loop, by which time [output_update] has already
   run: it leaves the state alone. *)
Definition input_update (Opub Opriv : Ty)
  (e : [Sum T_in (T_out Opub Opriv)]) (v : [state_type]) : [state_type] :=
  if e is inl i then set_pending i v else v.

(* The scheduler and the previous pid choose between the two user processes
   only, by a bit: [true] is the private user (pid inr 2, slot 4), [false]
   the public user (pid inr 3, slot 5).  So no scheduler, however it behaves,
   can install a handler or a padding slot: the model, not the scheduler,
   guarantees that the scheduler hands control to a user. *)
Definition user_pid (b : bool) : [cur_pid] := if b then inr 2 else inr 3.

Definition is_sched_out (Opub Opriv : Ty) (o : [T_out Opub Opriv]) :=
  match o with
  | (None,(None,(Some b,_))) => Some b
  | _ => None
  end.
Definition apply_scheduler_choice (Opub Opriv : Ty) (o : [T_out Opub Opriv]) (v : [state_type])  :=
  if is_sched_out o is Some b then update_cur_pid v (user_pid b) else v.

(* [apply_scheduler_choice] installs the user the scheduler's bit names as the
   current pid.  Note this reads the scheduler slot only -- the user slots are
   inspected for None-ness and nothing more (see [is_sched_out]), which is what
   keeps the state transition independent of what userspace does. *)

(* The pid of the handler an interrupt runs in. *)
Definition ir_handler_pid (ir : [irq]) : [cur_pid] :=
  match ir with
  | timer_irq => inr 0
  | disk_irq  => inl true
  | nop_irq   => inl false
  end.

(* It selects the slot the interrupt's own position in all_interrupts names. *)
Lemma slot_pid_ir_handler_pid : forall ir, slot_pid (ir_handler_pid ir) = index ir all_interrupts.
Proof. by case=> [[[]|[]]|]. Qed.

Definition is_handler_pid (v : [state_type]) :=
    match get_cur_pid v with
    | inr 0 => true
    | inr _ => false
    | _ => true
    end.

(* before overriding cur_pid, save it to prev_pid if it is a user process, so
   that control returns to that user.  Any other pid (a handler, the scheduler
   or padding) leaves prev_pid alone.  Only the value saved by the latest
   handler start from a user is ever read back, so prev_pid is never cleared. *)
Definition save_cur_to_prev (v : [state_type]) : [state_type] :=
  match get_cur_pid v with
  | inr 2 => update_prev_pid v true
  | inr 3 => update_prev_pid v false
  | _ => v
  end.

Definition initiate_handler (ir : [irq]) (v : [state_type]) :=
  update_ir_pending (set_masks (update_cur_pid (save_cur_to_prev v) (ir_handler_pid ir))) ir false.

(* a handler is selectable iff pending and not masked *)
Definition ir_ready (v : [state_type]) (ir : [irq]) : bool :=
  get_ir_pending v ir && ~~ get_ir_mask v ir.

Definition first_ready (v : [state_type]) : option [irq] :=
  ohead [seq ir <-  all_interrupts | (ir_ready v ir) ].

Definition scheduler_pid : [cur_pid] := inr 1.

Definition initiate_scheduler  (v : [state_type]) := update_re_sched (update_cur_pid v scheduler_pid) false.

Definition initiate_prev_pid  (v : [state_type]) := update_cur_pid v (user_pid (get_prev_pid v)).

(* Choose the next pid.  First install the scheduler's choice, if the scheduler
   has just run; then apply rules 1-4. *)
Definition initiate_next (Opub Opriv : Ty)
  (o : [T_out Opub Opriv]) (v : [state_type]) : [state_type] :=
  let v := apply_scheduler_choice o v in
  if (masks_set v) then v (*handler running*) else
             if first_ready v is Some ir then initiate_handler ir v (*first or later handler in the time slice is initiated here; inside a slice the NOP handler is always pending, so one runs*) else
               if is_handler_pid v then if get_re_sched v then initiate_scheduler v else initiate_prev_pid v  (*mask not set but we are in handler pid, we have just finished the time slice*) else
                 v (*we are running in user space*).



(* The [sta]'s output update.  An arriving interrupt only records itself;
   everything it eventually causes happens here, where the input is no longer
   the thing being varied.  That split is forced by f_EP, which under eqsum_LR,
   with no output unobservable, constrains the input update alone.  The policy has two stages:
   [observe_policy] reads the output, and [advance_policy] reads only the state,
   as its type says. *)
Definition output_update (Opub Opriv : Ty)
  (observe_policy : [T_out Opub Opriv] -> [state_type] -> [state_type])
  (advance_policy : [state_type] -> [state_type])
  (o : [T_out Opub Opriv]) : [state_type] -> [state_type] :=
  initiate_next o \o (advance_policy \o observe_policy o).

(* What one event of the model does to the state, for stating facts about whole
   runs.  The [sta] itself takes the two updates apart. *)
Definition state_step (Opub Opriv : Ty)
  (observe_policy : [T_out Opub Opriv] -> [state_type] -> [state_type])
  (advance_policy : [state_type] -> [state_type])
  (e : [Sum T_in (T_out Opub Opriv)]) (v : [state_type]) : [state_type] :=
  if e is inr o then output_update observe_policy advance_policy o v
  else input_update e v.


(* === 7. The generic model ===

   Everything above is shared.  A model is the process pool run inside the
   stateful wrapper, and the only freedom left is the triple

     (init_policy, observe_policy, advance_policy)

   that section 8 compares and the policy files fix.  Together they decide when a
   handler may run and form the *interrupt policy*; the [_policy] suffix marks
   them.  Note [runs] is not a parameter here: the slice size reaches the model
   only through [observe_policy], already applied. *)
Definition model (runtime : nat) (Opub Opriv : Ty)
  (init_policy : [state_type])
  (observe_policy : [T_out Opub Opriv] -> [state_type] -> [state_type])
  (advance_policy : [state_type] -> [state_type])
  (p_pub : Proc Empty Opub)
  (p_priv : Proc Bool Opriv)
  (p_sched : Proc Empty Bool) : Proc T_in (T_out Opub Opriv) :=
  @reactive_system cur_pid state_type init_policy T_in (T_out Opub Opriv) T_intermediate
    (@input_update Opub Opriv) (output_update observe_policy advance_policy) (no_output Opub Opriv)
    (pool runtime p_pub p_priv p_sched) (@pool_input Opub Opriv).

(* The user view of a model: [parse_output] on every output, keeping the two
   user slots and erasing the scheduler and all three handlers.  Like [model],
   it is shared by both policies. *)
Definition userview (Opub Opriv : Ty) (p : Proc T_in (T_out Opub Opriv))
  : Proc T_in (T_out_userview Opub Opriv) :=
  map id (@parse_output Opub Opriv) p.

Definition out_equiv_userview (Opub Opriv : Ty) : cEquiv [T_out_userview Opub Opriv] := eqmaybe_nobody (eqsum (public_equiv Opub) (private_equiv Opriv)).

(* The public view of a model: only the public user's output.  This is all an
   attacker needs to see the leak of [model_immediate]. *)
Definition public_output (Opub Opriv : Ty) (o : [T_out Opub Opriv]) : [Option Opub] := o.1.

Definition publicview (Opub Opriv : Ty) (p : Proc T_in (T_out Opub Opriv))
  : Proc T_in (Option Opub) :=
  map id (@public_output Opub Opriv) p.

Definition out_equiv_publicview (Opub : Ty) : cEquiv [Option Opub] := eqmaybe_nobody (public_equiv Opub).

(* === 8. The two policies, side by side ===

   The two policies, defined in model_immediate.v and model_sliced.v, are the
   same [model] at two different triples, and that
   difference is the whole security story:

     parameter            model_immediate            model_sliced
     -----------------------------------------------------------------------
     init_policy          immediate_init             sliced_init
                          no slice, no masks set     no slice, every
                                                     mask but the timer's set
     observe_policy       observe_handler_output     observe_timer_output runtime runs
                          a finished handler         a finished timer handler opens
                          unmasks everything, so     a slice and requests a
                          a pending interrupt is     reschedule
                          serviced at once
     advance_policy       id                         tick_slice runtime
                          nothing                    each handler boundary inside a
                                                     slice reopens the masks and
                                                     queues a NOP run; the slice is
                                                     counted down and closed on a
                                                     handler boundary

   In [model_immediate] a secret interrupt is therefore serviced the moment it
   arrives, displacing whatever was running; in [model_sliced] it can only be
   serviced inside a slice, where it replaces a NOP handler run of the same
   length. *)
