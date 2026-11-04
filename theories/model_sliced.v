
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
   model_sliced: [model] at the sliced policy, its slice invariant, the projected
   [model_sliced_userview], and their behaviour on the concrete system.
   ================================================================= *)

Definition mask_most : [ic] := ((false,true),((false,true),(false,false))). (*mask set for everything but timer interrupt*)

Definition sliced_init : [state_type] := ((initial_pid,None),(false,(0,mask_most))).

(* A handler boundary: the counter is a multiple of the handler length. *)
Definition slice_at_boundary (runtime m : nat) := dvdn runtime m.

(* The timer handler's completion opens a slice and, as in [model_immediate],
   requests a reschedule for when control next leaves the handlers.  The slice
   is a whole number [runs] of handler runs, [runs * runtime] steps, followed by
   the closing step.  Expressing it this way rather than as an independent
   constant is what makes "the slice ends on a handler boundary" structural
   instead of a side condition: [slice_at_boundary] can then *compute* the
   boundaries as the multiples of [runtime]. *)
Definition observe_timer_output (runtime runs : nat) (Opub Opriv : Ty) (o : [T_out Opub Opriv]) (v : [state_type]) : [state_type] :=
  if tI_out o is Some Notify
  then update_re_sched (update_slice_count v (runs * runtime).+1) true else v.

(* At a boundary: guarantee that the next step is a secret-handler run.  Unmask
   the disk and NOP handlers, mask the timer, and make the NOP handler pending,
   so the disk handler runs if it is pending and the NOP handler otherwise. *)
Definition queue_secret_run (v : [state_type]) : [state_type] :=
  update_ir_pending (set_tI (unset_masks v)) nop_irq true.

(* At the end of a slice: mask the disk and NOP handlers, unmask the timer, and
   disable the counter. *)
Definition close_slice (v : [state_type]) : [state_type] :=
  update_slice_count (unset_tI (set_masks v)) 0.

(* Advance an open slice by one step: count down, queue a secret run at each
   boundary, and close the slice at its closing step [1].  With the counter at
   [n.+2], [n.+1] steps of handler runs are left, and the boundary test is on
   those. *)
Definition tick_slice (runtime : nat) (v : [state_type]) : [state_type] :=
  match get_slice_count v with
  | 0    => v
  | 1    => close_slice v
  | n.+2 =>
      let v := update_slice_count v n.+1 in
      if slice_at_boundary runtime n.+1 then queue_secret_run v else v
  end.

(* The two stages together, the composite the proofs reason about. *)
Definition sliced_service (runtime runs : nat) (Opub Opriv : Ty) (o : [T_out Opub Opriv]) : [state_type] -> [state_type] := tick_slice runtime \o observe_timer_output runtime runs o.

(* model_sliced p_pub p_priv p_sched =
     model sliced_init (observe_timer_output runtime runs) (tick_slice runtime)
       p_pub p_priv p_sched *)
Definition model_sliced (runtime runs : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out Opub Opriv) :=
  model runtime sliced_init (@observe_timer_output runtime runs Opub Opriv) (tick_slice runtime)
    p_pub p_priv p_sched.


(* -- The slice invariant --

   The sliced policy keeps the secret handlers gated by the slice: outside a
   slice they are masked, inside one a handler is running, and the NOP and disk
   masks agree ([secret_gated]).  Every reachable state satisfies it
   (sliced_run_gated).  The security proof uses it through [sta_NI_pred], which
   asks for the relational obligations only on states that satisfy it.

   Where [initiate_next] chooses, a slice may also be at a handler boundary, in
   the shape [queue_secret_run] leaves ([secret_gated_at_boundary]).  What the
   security argument consumes is the consequence [secret_ready_iff_slice]: when
   no handler is running, a secret handler is ready exactly when a slice is
   open.  Whether a slice is open is public, so two related states agree on
   whether a secret handler runs next.

   The statements quantify over arbitrary event sequences, not only those a
   process pool can produce, so they need no reasoning about processes. *)

Definition slice_open (v : [state_type]) : bool := get_slice_count v != 0.

(* The shape [queue_secret_run] leaves: the NOP handler pending, the timer
   masked, the disk and NOP handlers unmasked. *)
Definition handler_boundary (w : [state_type]) : bool :=
  [&& get_ir_pending w nop_irq, get_ir_mask w timer_irq,
      ~~ get_ir_mask w disk_irq & ~~ get_ir_mask w nop_irq].

(* Inside a slice: [also] holds or a handler is running; outside: the disk
   handler is masked; always: the NOP and disk masks agree.  The disjunction
   follows the [if] in [tick_slice]. *)
Definition gated (also : [state_type] -> bool) (v : [state_type]) : bool :=
  (if slice_open v then also v || masks_set v else get_ir_mask v disk_irq) &&
  (get_ir_mask v nop_irq == get_ir_mask v disk_irq).

Definition secret_gated := gated (fun _ => false).
Definition secret_gated_at_boundary := gated handler_boundary.

Definition secret_ready (w : [state_type]) : bool :=
  ir_ready w disk_irq || ir_ready w nop_irq.

Definition secret_ready_iff_slice (w : [state_type]) : Prop :=
  ~~ masks_set w -> secret_ready w = slice_open w.

Section SlicedInvariant.
Variables (runtime runs : nat) (Opub Opriv : Ty).

Lemma masks_setE v : masks_set v =
  [&& get_ir_mask v timer_irq, get_ir_mask v disk_irq & get_ir_mask v nop_irq].
Proof. by rewrite /masks_set /= andbT. Qed.

(* The scheduler's choice writes only the current pid, which none of the
   predicates reads. *)
Lemma apply_scheduler_choice_gated (o : [T_out Opub Opriv]) w :
  [/\ masks_set (apply_scheduler_choice o w) = masks_set w,
      secret_gated (apply_scheduler_choice o w) = secret_gated w,
      secret_gated_at_boundary (apply_scheduler_choice o w) = secret_gated_at_boundary w,
      secret_ready (apply_scheduler_choice o w) = secret_ready w &
      slice_open (apply_scheduler_choice o w) = slice_open w].
Proof. rewrite /apply_scheduler_choice. by case: (is_sched_out o). Qed.

Lemma observe_timer_output_mask (o : [T_out Opub Opriv]) v ir :
  get_ir_mask (observe_timer_output runtime runs o v) ir = get_ir_mask v ir.
Proof. by rewrite /observe_timer_output; case: (tI_out o) => [[|]|]. Qed.

Lemma observe_timer_output_count (o : [T_out Opub Opriv]) v :
  get_slice_count (observe_timer_output runtime runs o v) =
  if tI_out o is Some Notify then (runs * runtime).+1 else get_slice_count v.
Proof. by rewrite /observe_timer_output; case: (tI_out o) => [[|]|]. Qed.

(* One lemma per branch of [tick_slice]. *)
Lemma tick_slice_close v : get_slice_count v = 1 ->
  [/\ get_slice_count (tick_slice runtime v) = 0,
      get_ir_mask (tick_slice runtime v) nop_irq = true &
      get_ir_mask (tick_slice runtime v) disk_irq = true].
Proof. rewrite /tick_slice => ->. by move: v => [[? ?] [? [? [[? ?] [[? ?] [? ?]]]]]]. Qed.

Lemma tick_slice_boundary v n : get_slice_count v = n.+2 ->
  slice_at_boundary runtime n.+1 ->
  [/\ get_slice_count (tick_slice runtime v) = n.+1,
      get_ir_mask (tick_slice runtime v) nop_irq = false,
      get_ir_mask (tick_slice runtime v) disk_irq = false,
      get_ir_mask (tick_slice runtime v) timer_irq = true &
      get_ir_pending (tick_slice runtime v) nop_irq = true].
Proof. rewrite /tick_slice => -> ->. by move: v => [[? ?] [? [? [[? ?] [[? ?] [? ?]]]]]]. Qed.

Lemma tick_slice_dec v n : get_slice_count v = n.+2 ->
  ~~ slice_at_boundary runtime n.+1 ->
  [/\ get_slice_count (tick_slice runtime v) = n.+1,
      forall ir, get_ir_mask (tick_slice runtime v) ir = get_ir_mask v ir &
      forall ir, get_ir_pending (tick_slice runtime v) ir = get_ir_pending v ir].
Proof. rewrite /tick_slice => -> /negbTE ->. by split => // -[]. Qed.

Lemma tick_slice_none v : get_slice_count v = 0 -> tick_slice runtime v = v.
Proof. by rewrite /tick_slice => ->. Qed.

(* Opening a slice lands on a boundary. *)
Lemma slice_at_boundary_start : slice_at_boundary runtime (runs * runtime).
Proof. by rewrite /slice_at_boundary dvdn_mull. Qed.

(* {secret_gated} sliced_service o {secret_gated_at_boundary} *)
Lemma sliced_service_gated (o : [T_out Opub Opriv]) v :
  secret_gated v -> secret_gated_at_boundary (sliced_service runtime runs o v).
Proof.
have -> : sliced_service runtime runs o v =
          tick_slice runtime (observe_timer_output runtime runs o v) by [].
set v1 := observe_timer_output runtime runs o v.
have M1 : forall ir, get_ir_mask v1 ir = get_ir_mask v ir by move=> ir; rewrite observe_timer_output_mask.
have C1 : get_slice_count v1 = if tI_out o is Some Notify then (runs * runtime).+1 else get_slice_count v
  by rewrite observe_timer_output_count.
rewrite /secret_gated /secret_gated_at_boundary /gated /slice_open => /andP [Hl /eqP Hdk].
case E1: (get_slice_count v1) => [|[|n]].
- (* no slice before, none after *)
  rewrite (tick_slice_none E1) E1 !M1 Hdk /= eqxx andbT.
  move: C1 Hl; rewrite E1.
  by case: (tI_out o) => [[|]|] // <-.
- (* closing: disk and NOP masked, no slice *)
  by case: (tick_slice_close E1) => -> -> ->.
- case HC: (slice_at_boundary runtime n.+1).
  + (* a boundary: the shape queue_secret_run leaves *)
    case: (tick_slice_boundary E1 HC) => -> Bd Bk Bt Bp.
    by rewrite /handler_boundary Bd Bk Bt Bp.
  + (* a plain tick inside a slice that was already open: masks unchanged *)
    case: (tick_slice_dec E1 (negbT HC)) => -> Tm Tp.
    rewrite masks_setE !Tm !M1 Hdk /= eqxx andbT orbC /=.
    move: C1 Hl; rewrite E1.
    case: (tI_out o) => [[|]|].
    * by move<-; rewrite /= masks_setE Hdk => ->.
    * (* a slice just opened lands on a boundary *)
      by case=> Hs; move: HC; rewrite Hs slice_at_boundary_start.
    * by move<-; rewrite /= masks_setE Hdk => ->.
Qed.

(* At the choice point the gating gives the fact the security proof uses. *)
Lemma secret_gated_at_boundary_ready w :
  secret_gated_at_boundary w -> secret_ready_iff_slice w.
Proof.
rewrite /secret_gated_at_boundary /gated /secret_ready_iff_slice /secret_ready /ir_ready.
case: (slice_open w) => /andP [H /eqP Hnd] Ms.
- move: H; rewrite (negbTE Ms) orbF => /and4P [-> _ _ ->].
  by rewrite orbT.
- by rewrite Hnd H !andbF.
Qed.

(* {secret_gated_at_boundary} initiate_next o {secret_gated} *)
Lemma initiate_next_gated (o : [T_out Opub Opriv]) w :
  secret_gated_at_boundary w -> secret_gated (initiate_next o w).
Proof.
rewrite /initiate_next.
case: (apply_scheduler_choice_gated o w) => _ _ <- _ _.
move: (apply_scheduler_choice o w) => {}w Hw.
case Ms: (masks_set w).
- move: Hw; rewrite /secret_gated_at_boundary /secret_gated /gated Ms orbT.
  by case: (slice_open w).
- case FR: (first_ready w) => [ir|].
  + move: w {Hw Ms FR} => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]].
    by case: ir => [[]|]; case: cur => [b|m]; case: c.
  + have NS : ~~ slice_open w.
      apply/negP => S; move: Hw.
      rewrite /secret_gated_at_boundary /gated S Ms orbF => /andP [/and4P [Hp _ _ Hnm] _].
      have Rd : ir_ready w nop_irq by rewrite /ir_ready Hp Hnm.
      move: FR; rewrite /first_ready /=.
      by case: (ir_ready w timer_irq); case: (ir_ready w disk_irq); rewrite ?Rd.
    have Hg : secret_gated w by move: Hw; rewrite /secret_gated_at_boundary /secret_gated /gated (negbTE NS).
    move: w Hg {Hw Ms FR NS} => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]] Hg.
    by case: (is_handler_pid _); first case: (get_re_sched _).
Qed.

(* {secret_gated} set_pending i {secret_gated}: an input writes only a pending
   bit, which [secret_gated] does not read. *)
Lemma set_pending_gated i v : secret_gated v -> secret_gated (set_pending i v).
Proof. by move: v => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]]; case: i => -[]. Qed.

Lemma sliced_init_gated : secret_gated sliced_init.
Proof. by []. Qed.

(* Both updates preserve [secret_gated]. *)
Lemma input_update_gated (e : [Sum T_in (T_out Opub Opriv)]) v :
  secret_gated v -> secret_gated (input_update e v).
Proof. by case: e => [i|o] Hv //; apply: set_pending_gated. Qed.

Lemma output_update_gated (o : [T_out Opub Opriv]) v :
  secret_gated v ->
  secret_gated (output_update (@observe_timer_output runtime runs Opub Opriv) (tick_slice runtime) o v).
Proof. by move=> Hv; apply: initiate_next_gated; apply: sliced_service_gated. Qed.

(* Every step preserves [secret_gated]. *)
Lemma state_step_gated (e : [Sum T_in (T_out Opub Opriv)]) v :
  secret_gated v ->
  secret_gated (state_step (@observe_timer_output runtime runs Opub Opriv) (tick_slice runtime) e v).
Proof.
case: e => [i|o] Hv; first exact: input_update_gated.
exact: output_update_gated.
Qed.

(* The state after any sequence of events, starting from [sliced_init]. *)
Definition sliced_run (es : seq [Sum T_in (T_out Opub Opriv)]) :=
  foldl (fun v e => state_step (@observe_timer_output runtime runs Opub Opriv) (tick_slice runtime) e v)
        sliced_init es.

Theorem sliced_run_gated es : secret_gated (sliced_run es).
Proof.
rewrite /sliced_run; elim/last_ind: es => [|es e IH]; first exact: sliced_init_gated.
by rewrite foldl_rcons; apply: state_step_gated.
Qed.

End SlicedInvariant.


(* === 9. model_sliced_userview === *)

Definition model_sliced_userview (runtime runs : nat) (Opub Opriv : Ty)
  (p_pub : Proc Empty Opub)
  (p_priv : Proc THandlerOutput Opriv)
  (p_sched : Proc Empty Nat) : Proc T_in (T_out_userview Opub Opriv) :=
  userview (model_sliced runtime runs p_pub p_priv p_sched).


(* The concrete slice: two handler runs. *)
Definition slice_runs := 2.
Definition model_sliced_concrete := model_sliced handler_runtime slice_runs p_pub_concrete p_priv_concrete scheduler.
Definition model_sliced_userview_concrete :=
  model_sliced_userview handler_runtime slice_runs p_pub_concrete p_priv_concrete scheduler.

(* Sanity, at this instance: the computed test agrees with the enumeration
   [2 | 4] it replaced, on every counter value [tick_slice] tests (the counter
   starts at [slice_runs * handler_runtime], and the test sees [Some n.+1]
   before each decrement). *)
Lemma slice_at_boundary_reachable n :
  n.+1 <= slice_runs * handler_runtime ->
  slice_at_boundary handler_runtime n.+1 = ((n.+1 == 2) || (n.+1 == 4)).
Proof. by case: n => [|[|[|[|n]]]]. Qed.

Definition sliced_no_dI' : seqtype' := [::out_get';out_get';out_get';tI';out_get';tmr_step';tmr_done';nop_step';nop_done';nop_step';nop_done';sched_priv';out_nop'].
Definition sliced_with_dI' : seqtype' := [::out_get';dI';out_get';out_get';tI';out_get';tmr_step';tmr_done';dsk_step';dsk_done';nop_step';nop_done';sched_priv';out_syscall'].

Lemma trace_sliced_no_dI' l : Trace (public_equiv _) l sliced_no_dI' model_sliced_concrete.
Proof. rewrite /model_sliced_concrete /model_sliced. rewr;simpl;rewr;simpl;rewr;simpl;rewr. do 12 trace_step. trace_last. Qed.

Lemma trace_sliced_with_dI' l : Trace (public_equiv _) l sliced_with_dI' model_sliced_concrete.
Proof. rewrite /model_sliced_concrete /model_sliced. rewr;simpl;rewr;simpl;rewr;simpl;rewr. do 13 trace_step. trace_last. Qed.


Definition sliced_states :=
  run_states sliced_init (@observe_timer_output handler_runtime slice_runs TPublicOutput TTypeSyscall)
             (tick_slice handler_runtime).

Lemma sliced_states_no_dI : seq.map state_row (sliced_states sliced_no_dI') =
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

Lemma sliced_states_with_dI : seq.map state_row (sliced_states sliced_with_dI') =
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


Corollary sliced_states_model l (es : seqtype') n :
  Trace (public_equiv _) l es model_sliced_concrete -> n < size es ->
  exists q', Steps (take n.+1 es) model_sliced_concrete
    (system (@observe_timer_output handler_runtime slice_runs TPublicOutput TTypeSyscall)
            (tick_slice handler_runtime)
            (nth sliced_init (sliced_states es) n) q').
Proof. exact: run_states_model. Qed.


(* -- model_sliced_userview traces -- *)

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
