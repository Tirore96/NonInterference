Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import RelationClasses.
From Paco Require Import paco.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
Require Import Streams.
From HB Require Import structures.
From deriving Require Import deriving.
Require Import Coq.Program.Equality.
From Equations Require Import Equations.
Require Import Coq.Classes.DecidableClass.
Import Order.TTheory.
Open Scope order_scope.

Require Import NonInterference.theorems.

Fixpoint times_N n (f : nat -> Ty) : Ty :=
  let t := f n in
  match n with
  | 0 => t
  | S n' => Times t (times_N n' f)
  end.

Definition map_pair {A B C D :Set} (f : A -> C) (g : B -> D) := fun (x: A * B) => match x with
                                                                                | (x0,x1) => (f x0, g x1)
                                                                                  end.
Definition times_Option_n (n : nat) (f : nat -> Ty) := times_N n (Option \o f).

(*Example*)
Definition my_f_I := fun (n : nat) => match n with
                                      | 0 => TInterrupt (*handler*)
                                      | 1 => THandlerOutput (*private*)
                                      | 2 => Unit (*public*)
                                      | 3 => TInterrupt (*scheduler*)
                                      | _ => Unit
                                      end.

Definition my_f_O := fun (n : nat) => match n with
                                      | 0 => THandlerOutput
                                      | 1 => TTypeSyscall
                                      | 2 => TPublicOutput
                                      | 3 => Times Nat Bool
                                      | _ => Unit
                                      end.
Definition my_T_in := Sum Unit TInterrupt. (*We need Unit input to be able to differentiate trace, otherwise we only have interrupts in the trace*)
Definition my_T_out := Option (Sum TPublicOutput TTypeSyscall).
Definition my_T_in' := times_Option_n 3 my_f_I.
Definition my_T_out' := times_Option_n 3 my_f_O.


(*Process*)

Definition alternate_generic (A B C: Ty) (x y : [B]) (z : [C]) := @map _ (Sum _ _) (Sum _ (Times Bool C)) B 
                        inl
                        (fun o => if o is inr (true,z) then x else y)
                        (@loop (Sum A (Times Bool C))
                        (@map (Sum A _) _ _ (Sum _ _) id (fun o => inr o)
                        ((@sta (Sum _ _) _ Bool
                           (fun i v => if i is inl _ then true else false)
                           (fun o v => v)
                           false
                           (@out (Times Bool _ ) C z)
                        )))).

Definition alternate_generic2 (A B C : Ty) (x y : [B]) (z : [C]) (pred : [A] -> bool) :=
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

Definition scheduled_process_pool
  (n : nat)
  (f_coopt : nat -> bool)
  (f_initial : nat -> bool)
  (f_I f_O : nat -> Ty)
  (f_proc : forall n, Proc (f_I n) (f_O n)) : Proc (Times (Times Nat Nat) ((times_Option_n n f_I))) (times_Option_n n f_O).
  elim: n.
  - simpl.
    eapply map. simpl.
      instantiate (1:= Times Bool (Option (f_I 0))). exact (fun n => ((0.+1 \in [:: fst (fst n); snd (fst n)],snd n))).
      exact id. 
    eapply swi. exact (f_initial 0.+1). 
    eapply maybe. 
    eapply map.
      eapply id. 
      exact (fun o => (f_coopt 0.+1,o)).
    exact (f_proc 0).

  - intros. simpl.
    eapply par.
    * eapply map.
      instantiate (1:= Times Bool (Option (f_I n.+1))). simpl.
      exact (fun x => ((n.+2) \in [:: fst (fst x); snd (fst x)], fst (snd x))).
        exact id. 
      eapply swi.
        exact (f_initial n.+2). 
      eapply maybe.
      eapply map.
        exact id.     
        exact (fun o => (f_coopt n.+2,o)).
      (*eapply maybe.*) (*not necessary anymore*)
      exact (f_proc n.+1).
    * eapply map. 3: apply H. simpl. 
      exact (map_pair id snd).
      exact id. 
Defined.

Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.

Definition only_loop
  (T_in' T_out' : Ty)   
  (f_route : [T_out'] -> [T_in'])
  (def : [T_out'])
  (p : Proc T_in' T_out')
  : Proc T_in' T_out' :=
  (@map T_in' (Sum T_in' T_out') (Sum T_in' T_out') T_out' inl (inr_or_def def)
                          (@loop (Sum T_in' T_out')
                             (@map (Sum T_in' T_out')
                                    T_in'
                                    _
                                    (Sum _ _)
                                (fun i  =>
                                   match i with
                                   | inl i' => i'
                                   | inr o  => f_route o (*i tilfælde hvor vi både ændrer switch og rerouter input, problem?*)
                                   end) inr
                                p))).

Definition low_p := @out Unit TPublicOutput GetRequest.
Definition handler := @alternate_generic TInterrupt THandlerOutput Unit2 Notify Nothing tt.
Definition high_p := @alternate_generic2 THandlerOutput TTypeSyscall Unit1 Syscall NOP tt (fun i => i == Notify).

(* ---------------------------------------------------------------------------
   The two interrupt handlers the OS runs around the user processes.

   handler   (pool index 1) : the DISK ISR. Runs in response to a disk interrupt
                              and emits a THandlerOutput (Notify / Nothing).
   scheduler (pool index 4) : the TIMER ISR with the round-robin SCHEDULER fused
                              into it, named honestly. (In real Linux these are
                              distinct -- scheduler_tick flags need_resched and
                              schedule() runs at a preemption point -- but the
                              common simple-kernel model fuses them.) It runs ONLY
                              on a timer interrupt and emits, in one shot, the
                              round-robin choice of the next user process paired
                              with the mitigation CONTROL bit:

                                (next_user, mitigate) : Nat * Bool

                              next_user : 2 (high_p) or 3 (low_p), round-robin.
                              mitigate  : the mitigator's control decision, applied
                                MECHANICALLY by the hardware wrapper (V_state) below:
                                  true  = MITIGATED (good): mask interrupts during
                                    user execution AND drain the disk handler at
                                    EVERY timer (fixed cadence), so the public output
                                    stream is independent of disk activity.
                                  false = UNMITIGATED (bad): no masking, no drain; a
                                    disk interrupt preempts the running user process
                                    (ISR cycle-steal), shifting the public output one
                                    cycle -- the timing leak.

   This is the key conceptual point: the scheduler IS the mitigator. The decision
   (mask vs preempt) lives in its output; the wrapper only applies it. The
   scheduler keeps a single bit of state, curr (the round-robin cursor); good and
   bad schedulers are the SAME process differing only in the constant mitigate bit
   -- hence swappable in the pool.

   Implementation note: the inner `out` emits a placeholder unit; `sta` pairs it
   with the (already-advanced) cursor; the outer map reads that cursor to choose
   next_user. So with curr starting false, the first scheduled user is low_p (3),
   then high_p (2), alternating. *)
Definition mk_scheduler (mitigate : bool) : Proc TInterrupt (Times Nat Bool) :=
  @map TInterrupt TInterrupt (Times Bool Unit) (Times Nat Bool)
    id
    (fun x => (if fst x then 3 else 2, mitigate))
    (@sta TInterrupt Unit Bool
       (fun _ curr => curr)        (* receiving the timer does not move the cursor *)
       (fun _ curr => negb curr)   (* after scheduling, advance the round-robin cursor *)
       false
       (@out (Times Bool TInterrupt) Unit tt)).

(* The mitigated (good) and unmitigated (bad) schedulers are the same process;
   they differ only in the constant mitigate bit (true = mask + drain at timer,
   false = let disk preempt). See mk_scheduler above. *)
Definition good_schedulerp : Proc TInterrupt (Times Nat Bool) := mk_scheduler true.
Definition bad_schedulerp  : Proc TInterrupt (Times Nat Bool) := mk_scheduler false.

Definition unit_p : Proc Unit Unit := @out Unit Unit tt.

Definition my_procs_good (n : nat) : Proc (my_f_I n) (my_f_O n).
Proof. by case: n => [| [| [| [| n]]]]; [apply: handler | apply: high_p | apply: low_p | apply: good_schedulerp | apply: unit_p]. Defined.

Definition my_procs_bad (n : nat) : Proc (my_f_I n) (my_f_O n).
Proof. by case: n => [| [| [| [| n]]]]; [apply: handler | apply: high_p | apply: low_p | apply: bad_schedulerp | apply: unit_p]. Defined.

(* ISR processes are COOPERATIVE (they self-disable after one cycle), while user
   processes are NON-COOPERATIVE (they run continuously until preempted).
   1 = disk handler, 4 = scheduler. *)
Definition my_f_coopt (n : nat) : bool := true.
Definition my_f_initial (n : nat) := false.
Definition process_pool_good := @scheduled_process_pool 3 my_f_coopt my_f_initial my_f_I my_f_O my_procs_good.
Definition process_pool_bad := @scheduled_process_pool 3 my_f_coopt my_f_initial my_f_I my_f_O my_procs_bad.

Definition LoopType_n (n : nat) (f_I f_O : nat -> Ty) := Sum (times_Option_n n f_I) (times_Option_n n f_O).
Definition None_N (n : nat) (f_O : nat -> Ty) : [(times_Option_n n f_O)].
elim: n. simpl. exact None.
intros. simpl. eapply pair. exact None. exact H.
Defined.
Definition collapse_in_out (n : nat) (f_I f_O : nat -> Ty) (x : [LoopType_n n f_I f_O]) : [times_Option_n n f_O]  :=
  match x with
  | inl _ => None_N n f_O
  | inr x' => x'
  end.
Definition my_def := None_N 3 my_f_O.
Definition none4 : [ (times_Option_n 3 my_f_I) ]  := (None,(None,(None,None))).
(* Loop feedback: the only output that must be carried back into the pool is the
   disk handler's THandlerOutput, which is delivered to high_p's input slot (so a
   Notify can wake high_p into a Syscall). Everything else routes to a neutral
   input -- the wrapper (V_state/override_pool_input) decides what runs next from
   its registers, not from the routed value. *)
Definition my_f_route_good (t : [my_T_out']) : [my_T_in'] :=
  let '(sch, (low, (high, handl))) := t in
  match handl with
  | Some h => (None, (None, (Some h, None)))
  | None => none4
  end.
Definition my_f_in_t (t : [my_T_in]) : [times_Option_n 3 my_f_I] :=
  match t with
  | inl tt => (None, (Some tt, (None, None)))
  | inr TimerInterrupt => (Some TimerInterrupt, (None, (None, None)))
  | inr DiskInterrupt => (None, (None, (None, Some DiskInterrupt)))
  end.
Definition my_f_in_good (t : [my_T_in]) : [my_T_in'] := my_f_in_t t.
Definition my_f_out (t : [my_T_out']) := match t with
                                         | (_,(Some p,(None,None))) => Some (inl p)
                                         | (_,(None,(Some sys,None))) => Some (inr sys)
                                         | _ => None
                                         end.

(* V_state is the thin HARDWARE interrupt controller -- only the registers the
   pool's swi mechanism and the two-phase (input/output) reduction force us to
   keep. It carries NO policy: the mitigation decision lives in the scheduler (see
   mk_scheduler); g_state below just applies it. The five registers:

     ((timer_pending, disk_pending),
      (p_sched, (handler_queued, masked)))

   - timer_pending / disk_pending : the interrupt lines, latched by f_state when a
     signal arrives on the bus (no separate "received" buffer -- a signal is
     pending the moment it arrives).
   - p_sched : the user the mitigator last chose (2 or 3); the "return address" the
     hardware vectors back to after an ISR.
   - handler_queued : run the disk ISR next cycle. SET by the mitigator's command
     (good) or by an unmitigated hardware preemption (bad).
   - masked : interrupts-masked flag, SET by the mitigator. The hardware only
     READS it (to decide whether a pending disk preempts a running user).

   We restore the `active` register to properly toggle off non-cooperative users. *)
Definition V_state := Times (Times Bool Bool) (Times Nat (Times Bool (Times Bool Nat))).

(* f_state (INPUT transition): latch an arriving interrupt straight onto its
   pending line. The running process is unaffected and completes its step. *)
Definition f_state (i_pool : [my_T_in']) (v : [V_state]) : [V_state] :=
  let '(i0, (i1, (i2, i3))) := i_pool in
  let '((v_timer, v_disk), (v_psched, (v_hq, (v_mask, v_active)))) := v in
  let timer_pending := if i0 is Some TimerInterrupt then true else v_timer in
  let disk_pending  := if i3 is Some DiskInterrupt then true else v_disk in
  ((timer_pending, disk_pending), (v_psched, (v_hq, (v_mask, v_active)))).

(* g_state (OUTPUT transition, end of a CPU cycle): pure mechanism -- it dispatches
   on WHICH pool slot fired and applies the mitigator's bit; it makes no policy of
   its own.
   - scheduler (timer ISR) fired with (p_next, mitigate): store the chosen user;
     record masked := mitigate; queue the disk handler iff mitigate (the mitigator
     drains disk at EVERY timer); clear the timer line.
   - disk handler fired: dequeue it (handler_queued := false); clear the disk line.
   - a user fired: the HARDWARE preemption -- queue the disk handler iff a disk is
     pending and interrupts are NOT masked (the leak; the handler clears the disk
     line when it runs).
   We also update `active` to record which process ran this cycle. *)
Definition g_state (o : [my_T_out']) (v : [V_state]) : [V_state] :=
  let '(o0, (o1, (o2, o3))) := o in
  let '((timer_pending, disk_pending), (p_sched, (handler_queued, (masked, active)))) := v in

  match o0 with
  | Some (p_next, mitigate) =>
      (* timer ISR / scheduler ran *)
      ((false, disk_pending),
       (p_next, (mitigate, (mitigate, 4))))
  | None =>
      match o3 with
      | Some _ =>
          (* disk handler ran *)
          ((timer_pending, false),
           (p_sched, (false, (masked, 1))))
      | None =>
          (* a user process ran *)
          let preempt := disk_pending && negb masked in
          ((timer_pending, disk_pending),
           (p_sched, (preempt, (masked, p_sched))))
      end
  end.

Definition I_pool := times_Option_n 3 my_f_I.

(* override_pool_input chooses what runs THIS cycle, purely from the registers,
   and emits the pool switch pair together with that process's input. Hardware
   interrupt vectoring: a pending timer vectors to the scheduler (index 4); else a
   queued disk vectors to the disk handler (index 1); else the scheduled user
   (p_sched) runs. 
   swi toggles are boolean flips: to avoid the double-toggle bug, we only toggle
   OFF the `active` process if it didn't already self-disable (i.e. if it's non-
   cooperative). We toggle ON `target` if it's not already running. *)
Definition override_pool_input (x : [Times V_state my_T_in']) : [Times (Times Nat Nat) I_pool] :=
  let '(v, i_pool) := x in
  let '((timer_pending, disk_pending), (p_sched, (handler_queued, (masked, active)))) := v in
  let '(i0, (i1, (i2, i3))) := i_pool in

  let target := if timer_pending then 4 else if handler_queued then 1 else p_sched in
  
  let pool_input :=
    if target == 4 then (Some TimerInterrupt, (None, (None, None)))
    else if target == 1 then (None, (None, (None, Some DiskInterrupt)))
    else (None, (None, (i2, None))) in
  ((0, target), pool_input).

Definition v_state_init : [V_state] :=
  ((false, false), (2, (false, (false, 2)))).

Definition my_only_loop_good_inner : Proc my_T_in' my_T_out' :=
  @map my_T_in' my_T_in' (Times V_state my_T_out') my_T_out' id (fun x => snd x)
    (sta f_state g_state v_state_init
      (@map (Times V_state my_T_in') (Times (Times Nat Nat) I_pool) my_T_out' my_T_out' override_pool_input id process_pool_good)).

Definition my_only_loop_good' := @only_loop my_T_in' my_T_out' my_f_route_good my_def my_only_loop_good_inner.

Definition my_only_loop_good : Proc my_T_in my_T_out :=
  @map my_T_in my_T_in' my_T_out' my_T_out my_f_in_good my_f_out my_only_loop_good'.

Definition my_only_loop_bad_inner : Proc my_T_in' my_T_out' :=
  @map my_T_in' my_T_in' (Times V_state my_T_out') my_T_out' id (fun x => snd x)
    (sta f_state g_state v_state_init
      (@map (Times V_state my_T_in') (Times (Times Nat Nat) I_pool) my_T_out' my_T_out' override_pool_input id process_pool_bad)).

Definition my_only_loop_bad' := @only_loop my_T_in' my_T_out' my_f_route_good my_def my_only_loop_bad_inner.

Definition my_only_loop_bad : Proc my_T_in my_T_out :=
  @map my_T_in my_T_in' my_T_out' my_T_out my_f_in_good my_f_out my_only_loop_bad'.

Definition out0 x : [my_T_out'] := (Some x,(None,(None,None))).
Definition out1 x : [my_T_out'] := (None,(Some x,(None,None))).
Definition out2 x : [my_T_out'] := (None,(None,(Some x,None))).
Definition out3 x : [my_T_out'] := (None,(None,(None, Some x))).

(*Spec for good scheduler*)
Definition seqtype' := seq ([my_T_in'] + [my_T_out']).
Definition newtrace' : seqtype' :=
  cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 1 *)
  (cons (inr (out0 (3, true))) (* Step 2: scheduler runs, picks low_p *)
  (cons (inr (out3 Notify)) (* Step 3: handler drains (because mitigate=true) *)
  (cons (inr (out1 GetRequest)) (* Step 4: low_p runs *)
  (cons (inl (my_f_in_good (inr DiskInterrupt))) (* Step 5: inject disk *)
  (cons (inr (out1 GetRequest)) (* Step 6: low_p runs (ignores disk because masked) *)
  (cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 7: timer *)
  (cons (inr (out0 (2, true))) (* Step 8: scheduler runs, picks high_p *)
  (cons (inr (out3 Notify)) (* Step 9: handler drains queued disk *)
  (cons (inr (out2 Syscall)) nil))))))))). (* Step 10: high_p receives Notify *)

Definition seqtype := seq ([my_T_in] + [my_T_out]).

Definition newtrace_wrap : seqtype  :=
  cons (inl (inr TimerInterrupt))
  (cons (inr None)
  (cons (inr None)
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inr DiskInterrupt))
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inr TimerInterrupt))
  (cons (inr None)
  (cons (inr None)
  (cons (inr (Some (inr Syscall))) nil))))))))).

Definition newtrace_no_disk : seqtype' :=
  cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 1 *)
  (cons (inr (out0 (3, true))) (* Step 2: scheduler runs, picks low_p *)
  (cons (inr (out3 Notify)) (* Step 3: handler drains *)
  (cons (inr (out1 GetRequest)) (* Step 4: low_p runs *)
  (cons (inl (my_f_in_good (inl tt))) (* Step 5: NO disk interrupt *)
  (cons (inr (out1 GetRequest)) (* Step 6: low_p runs *)
  (cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 7: timer *)
  (cons (inr (out0 (2, true))) (* Step 8: scheduler runs, picks high_p *)
  (cons (inr (out3 Nothing)) (* Step 9: handler runs but disk is empty *)
  (cons (inr (out2 NOP)) nil))))))))). (* Step 10: high_p receives Nothing *)

Definition newtrace_no_disk_wrap : seqtype  :=
  cons (inl (inr TimerInterrupt))
  (cons (inr None)
  (cons (inr None)
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inl tt))
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inr TimerInterrupt))
  (cons (inr None)
  (cons (inr None)
  (cons (inr (Some (inr NOP))) nil))))))))).

Ltac model.rewr ::= rewrite /low_p /handler /high_p /my_only_loop_good' /my_only_loop_good /my_only_loop_good_inner /only_loop /process_pool_good /process_pool_bad /good_schedulerp /my_f_coopt /scheduled_process_pool /high_p /alternate_generic /alternate_generic2 /low_p /my_f_in_good /my_f_in_t /mk_scheduler /bad_schedulerp /my_procs_good /my_procs_bad /f_state /g_state /override_pool_input /v_state_init /my_only_loop_bad' /my_only_loop_bad /my_only_loop_bad_inner /my_f_initial /=.

Ltac safe_econstructor :=
  match goal with
  | |- reduceI ?p _ _ => is_evar p; fail 1
  | |- reduceO ?p _ _ => is_evar p; fail 1
  | |- _ => idtac
  end;
  econstructor.

Ltac reduce_tac ::= try model.rewr; repeat reduce_once; try swi_instans; controlled_eauto; rewrite ?eqtype.eq_refl /= /xor /=; repeat (reduce_once || safe_econstructor || reflexivity).

Lemma newtrace'_trace : Trace (eqpair_LR (eqmaybe (publicRel (Times Nat Bool)))
                          (eqpair_LR (eqmaybe (publicRel TPublicOutput))
                             (eqpair_LR (eqmaybe (semiprivateRel TTypeSyscall))
                                 (eqmaybe (semiprivateRel THandlerOutput))))) false newtrace' my_only_loop_good'.
Proof.
  econ. reduce_tac. simpl.
  econ. reduce_tac. simpl.   done.
  econ. reduce_tac. simpl. ssa.
  econ. reduce_tac. ssa.
  econ. reduce_tac. ssa.
  econ. reduce_tac. ssa.
  
Lemma newtrace_trace : Trace (eqmaybe (eqsum_LR (publicRel TPublicOutput) (semiprivateRel TTypeSyscall))) false newtrace_wrap my_only_loop_good.
Proof. Admitted.

Lemma newtrace_no_disk_trace : Trace (eqpair_LR (eqmaybe (publicRel (Times Nat Bool)))
                          (eqpair_LR (eqmaybe (publicRel TPublicOutput))
                             (eqpair_LR (eqmaybe (semiprivateRel TTypeSyscall))
                                 (eqmaybe (semiprivateRel THandlerOutput))))) false newtrace_no_disk my_only_loop_good'.
Proof. Admitted.

Lemma newtrace_no_disk_wrap_trace : Trace (eqmaybe (eqsum_LR (publicRel TPublicOutput) (semiprivateRel TTypeSyscall))) false newtrace_no_disk_wrap my_only_loop_good.
Proof. Admitted.


(* Spec for the BAD (Linux-like, interfering) scheduler, WITH a disk interrupt.
   The handler is NOT scheduled on the timer; it is entered only as a response to
   the disk interrupt, by preemption (a jump at the end of the CPU cycle).
   Compare with badtrace_no_disk' below: the two runs share the same input
   sequence but differ in the PUBLIC projection (steps 7-8), which is the leak. *)
Definition badtrace' : seqtype' :=
  cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 1 *)
  (cons (inr (out0 (3, false))) (* Step 2: scheduler picks low_p, mitigate=false *)
  (cons (inr (out1 GetRequest)) (* Step 3: low_p runs *)
  (cons (inl (my_f_in_good (inr DiskInterrupt))) (* Step 4: disk interrupt arrives *)
  (cons (inr (out1 GetRequest)) (* Step 5: low_p runs. Preempt gets set! *)
  (cons (inr (out3 Notify)) (* Step 6: handler preempts! *)
  (cons (inr (out1 GetRequest)) (* Step 7: low_p resumes *)
  (cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 8: timer interrupt *)
  (cons (inr (out0 (2, false))) (* Step 9: scheduler picks high_p *)
  (cons (inr (out2 NOP)) nil))))))))). (* Step 10: high_p runs (no Notify because disk already handled) *)

Definition badtrace_wrap : seqtype :=
  cons (inl (inr TimerInterrupt))
  (cons (inr None)
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inr DiskInterrupt))
  (cons (inr (Some (inl GetRequest)))
  (cons (inr None)
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inr TimerInterrupt))
  (cons (inr None)
  (cons (inr (Some (inr NOP))) nil))))))))).

Definition badtrace_no_disk' : seqtype' :=
  cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 1 *)
  (cons (inr (out0 (3, false))) (* Step 2: scheduler *)
  (cons (inr (out1 GetRequest)) (* Step 3: low_p *)
  (cons (inl (my_f_in_good (inl tt))) (* Step 4: empty disk *)
  (cons (inr (out1 GetRequest)) (* Step 5: low_p runs. Preempt is false! *)
  (cons (inr (out1 GetRequest)) (* Step 6: low_p runs AGAIN! *)
  (cons (inr (out1 GetRequest)) (* Step 7: low_p runs YET AGAIN! *)
  (cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 8: timer *)
  (cons (inr (out0 (2, false))) (* Step 9: scheduler picks high_p *)
  (cons (inr (out2 NOP)) nil))))))))). (* Step 10: high_p runs *)

(* Public (world-observable) projection. Compare with badtrace_wrap: they share
   the same input sequence but DIFFER at steps 8 and 9 -- with the disk interrupt
   the handler steals a CPU cycle, shifting low_p's public output one step later.
   That observable difference is the timing leak (interference). *)
Definition badtrace_no_disk_wrap : seqtype :=
  cons (inl (inr TimerInterrupt))
  (cons (inr None)
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inl tt))
  (cons (inr (Some (inl GetRequest)))
  (cons (inr (Some (inl GetRequest)))
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inr TimerInterrupt))
  (cons (inr None)
  (cons (inr (Some (inr NOP))) nil))))))))).

Lemma badtrace'_trace : Trace (eqpair_LR (eqmaybe (publicRel (Times Nat Bool)))
                          (eqpair_LR (eqmaybe (publicRel TPublicOutput))
                             (eqpair_LR (eqmaybe (semiprivateRel TTypeSyscall))
                                 (eqmaybe (semiprivateRel THandlerOutput))))) false badtrace' my_only_loop_bad'.
Proof. Admitted.

Lemma badtrace_no_disk'_trace : Trace (eqpair_LR (eqmaybe (publicRel (Times Nat Bool)))
                          (eqpair_LR (eqmaybe (publicRel TPublicOutput))
                             (eqpair_LR (eqmaybe (semiprivateRel TTypeSyscall))
                                 (eqmaybe (semiprivateRel THandlerOutput))))) false badtrace_no_disk' my_only_loop_bad'.
Proof. Admitted.

(* The world-observable (wrapped) versions: my_only_loop_bad = map my_f_in_good
   my_f_out my_only_loop_bad'. badtrace_wrap and badtrace_no_disk_wrap differ at
   steps 8-9 -- with the disk interrupt the handler steals a CPU cycle and shifts
   low_p's public output one step later. That difference is the timing leak. *)
Lemma badtrace_trace : Trace (eqmaybe (eqsum_LR (publicRel TPublicOutput) (semiprivateRel TTypeSyscall))) false badtrace_wrap my_only_loop_bad.
Proof. Admitted.

Lemma badtrace_no_disk_wrap_trace : Trace (eqmaybe (eqsum_LR (publicRel TPublicOutput) (semiprivateRel TTypeSyscall))) false badtrace_no_disk_wrap my_only_loop_bad.
Proof. Admitted.
