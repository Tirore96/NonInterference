
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

Definition unmasked_service (runtime runs : nat) (Opub Opriv : Ty) (o : [T_out Opub Opriv]) : [state_type] -> [state_type] :=
  tick_unmasked runtime \o observe_timer_output runtime runs o.

Definition model_timer_unmasked (runtime runs : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out Opub Opriv) :=
  model runtime sliced_init (@observe_timer_output runtime runs Opub Opriv) (tick_unmasked runtime)
    p_pub p_priv p_sched.

Section TimerUnmaskedInvariant.
Variables (runtime runs : nat) (Opub Opriv : Ty).

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
Lemma unmasked_service_gated (o : [T_out Opub Opriv]) v :
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
    * by move<-; rewrite /= masks_setE => ->.
    * by case=> Hs; move: HC; rewrite Hs (slice_at_boundary_start runtime runs).
    * by move<-; rewrite /= masks_setE => ->.
Qed.

End TimerUnmaskedInvariant.
