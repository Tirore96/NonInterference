
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

Require Export NonInterference.theories.concrete_system.

(* =================================================================
   model_immediate: normal interrupt handling, [model] at the immediate policy,
   and its behaviour on the concrete system.
   ================================================================= *)

Definition false_ir_bits : [ir_bits] := (false,false).
Definition false_ic : [ic] := ((false,false),(false_ir_bits,false_ir_bits)).
Definition immediate_init : [state_type] := ((initial_pid,3),(false,(0,false_ic))).

(* Observe every handler's output: a finished handler unmasks everything, and a
   finished timer handler also requests a reschedule.  The two policies differ
   in which output they observe ([observe_timer_output] in model_sliced.v). *)
Definition observe_handler_output (Opub Opriv : Ty) (o : [T_out Opub Opriv]) (v : [state_type])  :=
  if is_ir_out_done o is Some ir then let v := unset_masks v in if ir is timer_irq then update_re_sched v true else v else v.

(* model_immediate p_pub p_priv p_sched =
     model immediate_init observe_handler_output id p_pub p_priv p_sched *)
Definition model_immediate (runtime : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out Opub Opriv) :=
  model runtime immediate_init (@observe_handler_output Opub Opriv) id
    p_pub p_priv p_sched.

Definition model_immediate_concrete := model_immediate handler_runtime p_pub_concrete p_priv_concrete scheduler.
Definition model_immediate_userview_concrete := userview model_immediate_concrete.
Definition model_immediate_publicview_concrete := publicview model_immediate_concrete.

Definition immediate_no_dI' : seqtype' := [::out_get';out_get';out_get';tI';out_get';tmr_step';tmr_done';sched_priv';out_nop';out_nop';out_nop';out_nop';out_nop'].
Definition immediate_with_dI' : seqtype' := [::out_get';dI';out_get';dsk_step';tI';dsk_done';tmr_step';tmr_done';sched_priv';out_syscall';out_nop';out_nop';out_nop';out_nop'].

Lemma trace_immediate_no_dI' l : Trace (public_equiv _) l immediate_no_dI' model_immediate_concrete.
Proof. rewrite /model_immediate_concrete /model_immediate. rewr;simpl;rewr;simpl;rewr;simpl;rewr. sta_state_reduce. do 12 trace_step. trace_last. Qed.

Lemma trace_immediate_with_dI' l : Trace (public_equiv _) l immediate_with_dI' model_immediate_concrete.
Proof. rewrite /model_immediate_concrete /model_immediate. rewr;simpl;rewr;simpl;rewr;simpl;rewr. do 13 trace_step. trace_last. Qed.

Definition immediate_states :=
  run_states immediate_init (@observe_handler_output TPublicOutput TTypeSyscall) id.

Lemma immediate_states_no_dI : seq.map state_row (immediate_states immediate_no_dI') =
  [:: (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, true, true, false, false);
      (0, true, true, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false)].
Proof. by vm_compute. Qed.

Lemma immediate_states_with_dI : seq.map state_row (immediate_states immediate_with_dI') =
  [:: (0, false, false, false, false);
      (0, false, false, true, false);
      (0, true, true, false, false);
      (0, true, true, false, false);
      (0, true, true, false, false);
      (0, true, true, false, false);
      (0, true, true, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false);
      (0, false, false, false, false)].
Proof. by vm_compute. Qed.

Corollary immediate_states_model l (es : seqtype') n :
  Trace (public_equiv _) l es model_immediate_concrete -> n < size es ->
  exists q', Steps (take n.+1 es) model_immediate_concrete
    (system (@observe_handler_output TPublicOutput TTypeSyscall) id
            (nth immediate_init (immediate_states es) n) q').
Proof. exact: run_states_model. Qed.

