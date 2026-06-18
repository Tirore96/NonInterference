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
Require Import Stdlib.Program.Equality.
From Equations Require Import Equations.
Require Import Stdlib.Classes.DecidableClass.

Import Order.TTheory.
Open Scope order_scope.

Require Export NonInterference.llmwork.theorems.


Require Import Classical.

Unset Implicit Arguments.

Lemma Proc_has_input : forall I O (p : Proc I O) i_in, exists p', reduceI p i_in p'.
Proof.
  intros I O p. induction p as [I O o_val | I I' O O' f g p IHp | I O V f g v p IHp | I O b p IHp | I O1 O2 p1 IHp1 p2 IHp2 | I p IHp | I O p IHp]; intros i_in.
  - exists (out o_val). apply reduce_outI.
  - destruct (IHp (f i_in)) as [p' Hred].
    exists (map f g p'). eapply reduce_mapI; [reflexivity | exact Hred].
  - destruct (IHp (f i_in v, i_in)) as [p' Hred].
    exists (sta f g (f i_in v) p'). eapply reduce_staI; [reflexivity | exact Hred].
  - destruct i_in as [b_in val_in].
    destruct (IHp val_in) as [p' Hred].
    exists (swi (xor b b_in) p'). eapply reduce_swiI; [reflexivity | exact Hred].
  - destruct (IHp1 i_in) as [p1' Hred1].
    destruct (IHp2 i_in) as [p2' Hred2].
    exists (par p1' p2'). eapply reduce_parI; eauto.
  - destruct (IHp i_in) as [p' Hred].
    exists (loop p'). eapply reduce_loopI; eauto.
  - destruct i_in as [val_in |].
    + destruct (IHp val_in) as [p' Hred].
      exists (maybe p'). apply reduce_maybeI2; eauto.
    + exists (maybe p). apply reduce_maybeI.
  Unshelve. all: auto.
Qed.

Lemma Proc_has_output : forall I O (p : Proc I O), exists o p', reduceO p o p'.
Proof.
  intros I O p. induction p as [I O o_val | I I' O O' f g p IHp | I O V f g v p IHp | I O b p IHp | I O1 O2 p1 IHp1 p2 IHp2 | I p IHp | I O p IHp].
  - exists o_val, (out o_val). apply reduce_outO.
  - destruct IHp as [o_val [p' Hred]].
    exists (g o_val), (map f g p'). eapply reduce_mapO; [reflexivity | exact Hred].
  - destruct IHp as [o_val [p' Hred]].
    exists (g o_val v, o_val), (sta f g (g o_val v) p'). eapply reduce_staO; [reflexivity | exact Hred].
  - destruct b.
    + destruct IHp as [[b_out o_val] [p' Hred]].
      exists (Some o_val), (swi (~~ b_out) p').
      eapply reduce_swiO2; [reflexivity | exact Hred].
    + exists None, (swi false p). apply reduce_swiO.
  - destruct IHp1 as [o1 [p1' Hred1]].
    destruct IHp2 as [o2 [p2' Hred2]].
    exists (o1, o2), (par p1' p2'). apply reduce_parO; auto.
  - destruct IHp as [o_val [p' Hred]].
    destruct (Proc_has_input I I p' o_val) as [p'' Hred_in].
    exists o_val, (loop p''). eapply reduce_loopO; eauto.
  - destruct IHp as [o_val [p' Hred]].
    exists o_val, (maybe p'). apply reduce_maybeO; auto.
Qed.

Lemma oblivious_swi : forall (I O : Ty) (ORel : myrel [O]) (BRel : myrel [Bool]) (p : Proc I (Times Bool O)) l b,
  ~ aware BRel true l ->
  oblivious (eqpair_R BRel ORel) p l ->
  oblivious (eqmaybe_swi ORel BRel) (swi b p) l.
Proof.
  intros I O ORel BRel p l b H_naware H_obl.
  set (R := fun (q : Proc (Times Bool I) (Option O)) =>
              exists b' p', q = swi b' p' /\ oblivious (eqpair_R BRel ORel) p' l).
  assert (H_R : R (swi b p)).
  { exists b, p. split; auto. }
  move: H_R.
  eapply paco1_acc.
  intros rr H_bot H_R_rr q H_Rq.
  destruct H_Rq as [b' [p' [Hq H_obl']]].
  subst q.
  eapply paco1_fold.
  constructor.
  + intros i q' H_redI.
    right. apply H_R_rr.
    dependent destruction H_redI.
    exists (xor b' b'0), p'0. split; auto.
    punfold H_obl'.
    dependent destruction H_obl'.
    move: (H i0 p'0 H_redI) => [H_p'0 | H_bot_p'0]; [exact H_p'0 | contradiction].
  + intros o q' H_redO.
    dependent destruction H_redO.
    * split.
      { right. apply H_R_rr. exists false, p'. split; auto. }
      { simpl. exact H_naware. }
    * punfold H_obl'.
      dependent destruction H_obl'.
      move: (H0 (b0, o0) p'0 H_redO) => [H_p'0 H_dis].
      destruct H_p'0 as [H_p'0 | H_bot_p'0]; [| contradiction].
      apply dis_eqpair_R in H_dis.
      split.
      { right. apply H_R_rr. exists (~~ b0), p'0. split; auto. }
      { simpl. exact H_dis. }
Qed.

Fixpoint all_outputs_dis (I O : Ty) (ORel : myrel [O]) (l : level) (t : seq ([I] + [O])) : Prop :=
  match t with
  | nil => True
  | inl _ :: t' => all_outputs_dis I O ORel l t'
  | inr o :: t' => dis ORel l o /\ all_outputs_dis I O ORel l t'
  end.

Lemma oblivious_trace_any : forall (I O : Ty) (ORel : myrel [O]) (l : level) (p : Proc I O) t,
  oblivious ORel p l ->
  all_outputs_dis I O ORel l t ->
  Trace ORel l t p.
Proof.
  intros I O ORel l p t.
  elim: t p.
  - intros p H_obl H_dis. apply TR0.
  - intros [i | o] t IH p H_obl H_dis.
    + simpl in H_dis.
      destruct (Proc_has_input I O p i) as [p' HredI].
      eapply TR1; [exact HredI |].
      punfold H_obl. dependent destruction H_obl.
      destruct (H i p' HredI) as [H_p' | H_bot]; [| contradiction].
      apply IH; [exact H_p' | exact H_dis].
    + simpl in H_dis. destruct H_dis as [H_dis_o H_dis_t].
      destruct (Proc_has_output I O p) as [o' [p' HredO]].
      punfold H_obl. dependent destruction H_obl.
      destruct (H0 o' p' HredO) as [H_obl' H_dis_o'].
      have H_rel: rel ORel l o' o.
      { destruct ORel as [dis rel equiv r d i0]. simpl in *.
        move: (i0 l o' H_dis_o' o) => [H_impl1 H_impl2].
        apply H_impl1; auto. }
      destruct H_obl' as [H_obl' | H_bot]; [| contradiction].
      eapply TR2; [exact HredO | exact H_rel |].
      apply IH; [exact H_obl' | exact H_dis_t].
Qed.

Lemma oblivious_trace_dis : forall (I O : Ty) (ORel : myrel [O]) (l : level) (p : Proc I O) t,
  oblivious ORel p l ->
  Trace ORel l t p ->
  all_outputs_dis I O ORel l t.
Proof.
  intros I O ORel l p t H_obl H_tr.
  elim: H_tr H_obl.
  - intros p0 H_obl. simpl. auto.
  - intros p0 i p'0 t0 H_redI H_tr' IH H_obl.
    simpl. apply IH.
    punfold H_obl. dependent destruction H_obl.
    destruct (H i p'0 H_redI) as [H_p'0 | H_bot]; [exact H_p'0 | contradiction].
  - intros p0 o' o p'0 t0 H_redO H_rel H_tr' IH H_obl.
    simpl. split.
    + punfold H_obl. dependent destruction H_obl.
      destruct (H0 o' p'0 H_redO) as [H_obl' H_dis_o'].
      destruct ORel as [dis rel equiv r d i0]. simpl in *.
      move: (i0 l o' H_dis_o' o) => [H_impl1 H_impl2].
      apply H_impl2; auto.
    + apply IH.
      punfold H_obl. dependent destruction H_obl.
      destruct (H0 o' p'0 H_redO) as [H_obl' H_dis_o'].
      destruct H_obl' as [H_obl' | H_bot_p']; [exact H_obl' | contradiction].
Qed.

Lemma all_outputs_dis_insert_inl : forall I O (ORel : myrel [O]) l t n i,
  all_outputs_dis I O ORel l (insert n (inl i) t) <-> all_outputs_dis I O ORel l t.
Proof.
  intros I O ORel l t n i.
  elim: t n.
  - intros n. destruct n; simpl; tauto.
  - intros a t0 IH n. destruct n; simpl.
    + tauto.
    + destruct a; simpl; intuition.
Qed.

Lemma oblivious_NI_l : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (p : Proc I O) l,
  oblivious ORel p l ->
  NI_l IRel ORel l p.
Proof.
  intros I O IRel ORel p l H_obl.
  split; [| split].
  - intros t i i' n H_rel H_tr.
    have H_dis: all_outputs_dis I O ORel l (insert n (inl i) t).
    { eapply oblivious_trace_dis; eauto. }
    have H_dis': all_outputs_dis I O ORel l (insert n (inl i') t).
    { rewrite all_outputs_dis_insert_inl in H_dis.
      rewrite all_outputs_dis_insert_inl. exact H_dis. }
    eapply oblivious_trace_any; eauto.
  - intros t i n H_dis H_tr.
    have H_dis_t: all_outputs_dis I O ORel l t.
    { eapply oblivious_trace_dis; eauto. }
    have H_dis': all_outputs_dis I O ORel l (insert n (inl i) t).
    { rewrite all_outputs_dis_insert_inl. exact H_dis_t. }
    eapply oblivious_trace_any; eauto.
  - intros t i n H_dis H_tr.
    have H_dis_t: all_outputs_dis I O ORel l (insert n (inl i) t).
    { eapply oblivious_trace_dis; eauto. }
    have H_dis': all_outputs_dis I O ORel l t.
    { rewrite all_outputs_dis_insert_inl in H_dis_t. exact H_dis_t. }
    eapply oblivious_trace_any; eauto.
Qed.

Set Implicit Arguments.

Theorem swi_NI : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (BRel : myrel [Bool]) p b,
(forall l, aware BRel true l \/  oblivious (eqpair_R BRel ORel) p l ) -> NI IRel (eqpair_LR BRel ORel) p ->                                
NI (eqpair_LR BRel IRel) (eqmaybe_swi ORel BRel) (swi b p).
Proof.
  intros I O IRel ORel BRel p b H_aware_ob H_NI_p.
  intro l.
  (* We use classic here because aware is not constructively decidable in the logic.
     If the relation and dis were constructively decidable, a constructive decision
     procedure could be used instead of classical logic. *)
  destruct (classic (aware BRel true l)) as [H_aware | H_naware].
  - split; [| split].
    + intros t [bi val_i] [bi' val_i'] n Hrel Htr.
      apply rel_eqpair_LR in Hrel as [Hrel_b Hrel_i].
      have Heq_b: bi = bi'.
      { destruct bi, bi'; auto.
        - move: (H_aware false Hrel_b) => [H_false _]. done.
        - move: (equiv BRel l) => [? Hsym ?].
          have Hsym_rel := Hsym _ _ Hrel_b.
          move: (H_aware false Hsym_rel) => [H_false _]. done. }
      subst bi'.
      apply swi_trace in Htr as [t_p [Htr_p Hswi_tr]].
      have [n' [t_p' [Ht_p' Hswi_tr']]]: exists n' t_p', t_p = insert n' (inl val_i) t_p' /\ SwiTrace ORel BRel l b (insert n (inl (bi, val_i')) t) (insert n' (inl val_i') t_p').
      { eapply (swi_trace_swap (I:=I) (O:=O) (ORel:=ORel) (BRel:=BRel) (l:=l) (b:=b) (t:=t) (t_p:=t_p) (n:=n) (i:=(bi, val_i)) (i':=(bi, val_i'))); auto. }
      subst t_p.
      move: (H_NI_p l) => [H_NI_p1 _].
      have Htr_p': Trace (eqpair_LR BRel ORel) l (insert n' (inl val_i') t_p') p.
      { eapply H_NI_p1; [apply Hrel_i | apply Htr_p]. }
      eapply swi_conv; [apply H_aware | apply Htr_p' | apply Hswi_tr'].
    + intros t [bi val_i] n Hdis Htr.
      apply dis_eqpair_LR in Hdis as [Hdis_b Hdis_i].
      apply swi_trace in Htr as [t_p [Htr_p Hswi_tr]].
      have [n' Hswi_tr']: exists n', SwiTrace ORel BRel l b (insert n (inl (bi, val_i)) t) (insert n' (inl val_i) t_p).
      { eapply (swi_trace_insert_conv n); eauto. }
      move: (H_NI_p l) => [_ [H_NI_p2 _]].
      have Htr_p': Trace (eqpair_LR BRel ORel) l (insert n' (inl val_i) t_p) p.
      { eapply H_NI_p2; [apply Hdis_i | apply Htr_p]. }
      eapply swi_conv; [apply H_aware | apply Htr_p' | apply Hswi_tr'].
    + intros t [bi val_i] n Hdis Htr.
      apply dis_eqpair_LR in Hdis as [Hdis_b Hdis_i].
      apply swi_trace in Htr as [t_p [Htr_p Hswi_tr]].
      have [n' [t_p' [Ht_p' Hswi_tr']]]: exists n' t_p', t_p = insert n' (inl val_i) t_p' /\ SwiTrace ORel BRel l b t t_p'.
      { eapply (swi_trace_remove (I:=I) (O:=O) (ORel:=ORel) (BRel:=BRel) (l:=l) (b:=b) (t:=t) (t_p:=t_p) (n:=n) (i:=(bi, val_i))); auto. }
      subst t_p.
      move: (H_NI_p l) => [_ [_ H_NI_p3]].
      have Htr_p': Trace (eqpair_LR BRel ORel) l t_p' p.
      { eapply H_NI_p3; [apply Hdis_i | apply Htr_p]. }
      eapply swi_conv; [apply H_aware | apply Htr_p' | apply Hswi_tr'].
    + destruct (H_aware_ob l) as [H_aware_temp | H_oblivious].
      * contradiction.
      * apply oblivious_NI_l. eapply oblivious_swi; eauto.
Qed.
