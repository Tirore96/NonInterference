
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
                                      | _ => Unit
                                      end.

Definition my_f_O := fun (n : nat) => match n with
                                      | 0 => THandlerOutput
                                      | 1 => TTypeSyscall
                                      | 2 => TPublicOutput
                                      | _ => Unit
                                      end.



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

Definition process_pool
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

Definition nbstate := Times Bool (Times Bool Bool).
Definition b_to_n (bb : [Times Bool Bool]) := 
Definition loop_and_count
  (T_in T_in' T_out' : Ty)                
  (f_I : [Sum T_in T_out'] -> [nbstate] -> [nbstate])
  (n_state : nat)           
  (f_route : [T_out'] -> [T_in'])
  (def : [T_out'])
  (p : Proc (Times (Times Nat Nat) T_in') T_out')
  (f_map : [T_in] -> [T_in'])
  : Proc T_in T_out' :=
  (@map T_in (Sum T_in T_out') (Sum T_in T_out') T_out' inl (inr_or_def def)
                          (@loop (Sum T_in T_out')
                             (@map _ _ (Times _ _) _
                                id snd
                                (@sta _ _ nbstate f_I (fun _ v => v) (false,(true,true))
                                   (@map (Times nbstate (Sum _ _ ))
                                      (Times (Times Nat Nat) T_in')
                                _ (Sum _ _)
                                (fun i  =>
                                   match snd i with
                                   | inl i' => let nn := if fst (fst i) then snd (fst i) else (,3) in (nn,f_map i')
                                   | inr o  => ((3,3),f_route o) (*i tilfælde hvor vi både ændrer switch og rerouter input, problem?*)
                                   end) inr
                                p))))).


Definition low_p := @out Unit TPublicOutput GetRequest.
Definition handler := @alternate_generic TInterrupt THandlerOutput Unit2 Notify Nothing tt.
Definition high_p := @alternate_generic2 THandlerOutput TTypeSyscall Unit1 Syscall NOP tt (fun i => i == Notify).
Definition unit_p : Proc Unit Unit := @out Unit Unit tt.

Definition my_procs : forall n, Proc (my_f_I n) (my_f_O n).
  case. apply handler.
  case. apply high_p.
  case. apply low_p.
  elim. apply unit_p.
  intros. apply unit_p.
Defined.

Definition my_f_coopt (n : nat) : bool := false.
Definition my_f_initial (n : nat) := false.
Definition process_pool_good := @process_pool 2 my_f_coopt my_f_initial my_f_I my_f_O my_procs.

Definition my_T_in := Sum Unit TInterrupt. (*We need Unit input to be able to differentiate trace, otherwise we only have interrupts in the trace*)
Definition my_T_out := Option (Sum TPublicOutput TTypeSyscall).
Definition my_T_in' := times_Option_n 2 my_f_I.
Definition my_T_out' := times_Option_n 2 my_f_O.

Definition good_schedule (i : [Sum my_T_in my_T_out']) (v : [nbstate]) : [nbstate] :=
  match i with
  | inl (inl TimerInterrupt) => if
        
Definition model := loop_and_count my_T_in my_T_in' my_T_out' 







(* ISR processes are COOPERATIVE (they self-disable after one cycle), while user
   processes are NON-COOPERATIVE (they run continuously until preempted).
   1 = disk handler, 4 = scheduler. *)


Definition process_pool_bad := @scheduled_process_pool 3 my_f_coopt my_f_initial my_f_I my_f_O my_procs_bad.


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
