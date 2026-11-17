
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

Require Export NonInterference.theories.model_sliced.

(* =================================================================
   model_timer_unmasked: [model] at a second instance of the general theorem
   [model_policy_NI].  It is the sliced policy, except that a boundary leaves the
   timer unmasked.  The timer handler can then run inside a slice, and its
   completion reloads the counter, so masking the timer fixes the length of a
   slice and is not what security rests on.
   ================================================================= *)

Definition queue_unmasked (v : [state_type]) : [state_type] :=
  update_ir_pending (unset_masks v) nop_irq true.

Definition tick_unmasked (runtime : nat) (v : [state_type]) : [state_type] :=
  match get_slice_count v with
  | 0    => v
  | 1    => close_slice v
  | n.+2 =>
      let v := update_slice_count v n.+1 in
      if slice_at_boundary runtime n.+1 then queue_unmasked v else v
  end.

Definition unmasked_service (runtime runs : nat) (o : [T_out]) : [state_type] -> [state_type] :=
  tick_unmasked runtime \o observe_timer_output runtime runs o.

Definition model_timer_unmasked (runtime runs : nat)  (p_pub : Proc Empty Unit)
  (p_priv : Proc Bool Bool)
  (p_sched : Proc Empty Bool) : Proc T_in (T_out) :=
  model runtime sliced_init (@observe_timer_output runtime runs) (tick_unmasked runtime)
    p_pub p_priv p_sched.

Section TimerUnmaskedInvariant.
Variables (runtime runs : nat).

(* The branches of [tick_unmasked], as for [tick_slice]. *)
Lemma tick_unmasked_close v : get_slice_count v = 1 ->
  [/\ get_slice_count (tick_unmasked runtime v) = 0,
      get_ir_mask (tick_unmasked runtime v) nop_irq = true &
      get_ir_mask (tick_unmasked runtime v) disk_irq = true].
Proof. rewrite /tick_unmasked => ->. by move: v => [[? ?] [? [? [[? ?] [[? ?] [? ?]]]]]]. Qed.

Lemma tick_unmasked_boundary v n : get_slice_count v = n.+2 ->
  slice_at_boundary runtime n.+1 ->
  [/\ get_slice_count (tick_unmasked runtime v) = n.+1,
      get_ir_mask (tick_unmasked runtime v) nop_irq = false &
      get_ir_pending (tick_unmasked runtime v) nop_irq = true].
Proof. rewrite /tick_unmasked => -> ->. by move: v => [[? ?] [? [? [[? ?] [[? ?] [? ?]]]]]]. Qed.

Lemma tick_unmasked_dec v n : get_slice_count v = n.+2 ->
  ~~ slice_at_boundary runtime n.+1 ->
  [/\ get_slice_count (tick_unmasked runtime v) = n.+1,
      forall ir, get_ir_mask (tick_unmasked runtime v) ir = get_ir_mask v ir &
      forall ir, get_ir_pending (tick_unmasked runtime v) ir = get_ir_pending v ir].
Proof. rewrite /tick_unmasked => -> /negbTE ->. by split => // -[]. Qed.

Lemma tick_unmasked_none v : get_slice_count v = 0 -> tick_unmasked runtime v = v.
Proof. by rewrite /tick_unmasked => ->. Qed.

(* {secret_gated} unmasked_service o {secret_gated_at_boundary} *)
Lemma unmasked_service_gated (o : [T_out]) v :
  secret_gated v -> secret_gated_at_boundary (unmasked_service runtime runs o v).
Proof.
have -> : unmasked_service runtime runs o v =
          tick_unmasked runtime (observe_timer_output runtime runs o v) by [].
set v1 := observe_timer_output runtime runs o v.
have M1 : forall ir, get_ir_mask v1 ir = get_ir_mask v ir by move=> ir; rewrite observe_timer_output_mask.
have C1 : get_slice_count v1 = if tI_out o is Some Notify then (runs * runtime).+1 else get_slice_count v
  by rewrite observe_timer_output_count.
rewrite /secret_gated /secret_gated_at_boundary /gated /slice_open => Hl.
case E1: (get_slice_count v1) => [|[|n]].
- rewrite (tick_unmasked_none E1) E1 !M1 /=.
  move: C1 Hl; rewrite E1.
  by case: (tI_out o) => [[|]|] // <-.
- by case: (tick_unmasked_close E1) => -> -> ->.
- case HC: (slice_at_boundary runtime n.+1).
  + case: (tick_unmasked_boundary E1 HC) => -> Bd Bp.
    by rewrite /secret_ready /ir_ready Bd Bp orbT.
  + case: (tick_unmasked_dec E1 (negbT HC)) => -> Tm Tp.
    rewrite masks_setE !Tm !M1 /= orbC /=.
    move: C1 Hl; rewrite E1.
    case: (tI_out o) => [[|]|].
    * by case=> Hs; move: HC; rewrite Hs (slice_at_boundary_start runtime runs).
    * by move<-; rewrite /= masks_setE => ->.
    * by move<-; rewrite /= masks_setE => ->.
Qed.

End TimerUnmaskedInvariant.


(* The concrete instance, with the slice of model_sliced.v. *)
Definition model_timer_unmasked_concrete :=
  model_timer_unmasked handler_runtime slice_runs p_pub_concrete p_priv_concrete scheduler.

(* With no timer interrupt inside a slice the runs are those of [model_sliced]. *)
Lemma trace_timer_unmasked_no_dI' l : Trace (public_equiv _) l sliced_no_dI' model_timer_unmasked_concrete.
Proof. rewrite /model_timer_unmasked_concrete /model_timer_unmasked. rewr;simpl;rewr;simpl;rewr;simpl;rewr. do 12 trace_step. trace_last. Qed.

Lemma trace_timer_unmasked_with_dI' l : Trace (public_equiv _) l sliced_with_dI' model_timer_unmasked_concrete.
Proof. rewrite /model_timer_unmasked_concrete /model_timer_unmasked. rewr;simpl;rewr;simpl;rewr;simpl;rewr. do 13 trace_step. trace_last. Qed.

(* A timer interrupt arrives during the first NOP run.  At the next boundary the
   timer handler runs, inside the slice, and its completion reloads the counter:
   the slice lasts eight output steps where [sliced_no_dI'] has four. *)
Definition timer_in_slice' : seqtype' := [::out_get';out_get';out_get';tI';out_get';tmr_step';tmr_done';nop_step';tI';nop_done';tmr_step';tmr_done';nop_step';nop_done';nop_step';nop_done';sched_priv';out_nop'].

Lemma trace_timer_in_slice' l : Trace (public_equiv _) l timer_in_slice' model_timer_unmasked_concrete.
Proof. rewrite /model_timer_unmasked_concrete /model_timer_unmasked. rewr;simpl;rewr;simpl;rewr;simpl;rewr. do 17 trace_step. trace_last. Qed.


Definition timer_unmasked_states :=
  run_states sliced_init (@observe_timer_output handler_runtime slice_runs)
             (tick_unmasked handler_runtime).

Lemma timer_unmasked_states_no_dI : seq.map state_row (timer_unmasked_states sliced_no_dI') =
  [:: (0, false, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false);
      (0, true, true, false, false);
      (0, true, true, false, false);
      (4, true, true, false, false);
      (3, true, true, false, false);
      (2, true, true, false, false);
      (1, true, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false)].
Proof. by vm_compute. Qed.

Lemma timer_unmasked_states_with_dI : seq.map state_row (timer_unmasked_states sliced_with_dI') =
  [:: (0, false, true, false, false);
      (0, false, true, true, false);
      (0, false, true, true, false);
      (0, false, true, true, false);
      (0, false, true, true, false);
      (0, true, true, true, false);
      (0, true, true, true, false);
      (4, true, true, false, true);
      (3, true, true, false, true);
      (2, true, true, false, false);
      (1, true, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false)].
Proof. by vm_compute. Qed.

Lemma timer_unmasked_states_in_slice : seq.map state_row (timer_unmasked_states timer_in_slice') =
  [:: (0, false, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false);
      (0, true, true, false, false);
      (0, true, true, false, false);
      (4, true, true, false, false);
      (3, true, true, false, false);
      (3, true, true, false, false);
      (2, true, true, false, true);
      (1, true, true, false, true);
      (4, true, true, false, false);
      (3, true, true, false, false);
      (2, true, true, false, false);
      (1, true, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false);
      (0, false, true, false, false)].
Proof. by vm_compute. Qed.


Corollary timer_unmasked_states_model l (es : seqtype') n :
  Trace (public_equiv _) l es model_timer_unmasked_concrete -> n < size es ->
  exists q', Steps (take n.+1 es) model_timer_unmasked_concrete
    (system (@observe_timer_output handler_runtime slice_runs)
            (tick_unmasked handler_runtime)
            (nth sliced_init (timer_unmasked_states es) n) q').
Proof. exact: run_states_model. Qed.
