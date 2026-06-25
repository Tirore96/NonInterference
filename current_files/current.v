
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


Definition eqpair_dom (V I : Ty) (VRel : myrel [V]) (IRel : myrel [I])
   (P : [Times V I] -> Prop)
   (Hclo : forall l x y, rel VRel l x.1 y.1 -> rel IRel l x.2 y.2 -> P x -> P y)
   : myrel [Times V I].
  refine (@MyRel _
    (fun l x => dis IRel l x.2 /\ P x)
    (fun l x y => (rel VRel l x.1 y.1 /\ rel IRel l x.2 y.2)
                  \/ ((dis IRel l x.2 /\ P x) /\ (dis IRel l y.2 /\ P y)))
    _ _ _ _).
  - intro l. constructor.
    + intro x. left. split; apply rel_refl.
    + intros x y H. destruct H as [[H1 H2]|[Hx Hy]].
      * left. split; apply rel_sym; assumption.
      * right. split; assumption.
    + intros x y z Hxy Hyz.
      destruct Hxy as [[Hxy1 Hxy2]|[[Hdx Hpx] [Hdy Hpy]]];
      destruct Hyz as [[Hyz1 Hyz2]|[[Hdy' Hpy'] [Hdz Hpz]]].
      * left. split; eapply rel_trans; eauto.
      * right. split.
        -- split.
           ++ eapply dis_rel_dis2. apply Hdy'. apply Hxy2.
           ++ eapply Hclo. apply rel_sym; apply Hxy1. apply rel_sym; apply Hxy2. apply Hpy'.
        -- split; assumption.
      * right. split.
        -- split; assumption.
        -- split.
           ++ eapply dis_rel_dis. apply Hdy. apply Hyz2.
           ++ eapply Hclo. apply Hyz1. apply Hyz2. apply Hpy.
      * right. split; split; assumption.
  - intros l0 l1 Hord a0 a1 [[Hv Hi]|[[Hd0 Hp0][Hd1 Hp1]]].
    + left. split; eapply myrel_rule1; eauto.
    + right. split; split; try assumption; eapply myrel_rule2; eauto.
  - intros l0 l1 Hord a [Hd Hp]. split; [eapply myrel_rule2; eauto | assumption].
  - intros l a0 [Hd0 Hp0] a1. split.
    + intros [Hd1 Hp1]. right. split; split; assumption.
    + intros [[Hvv Hii]|[_ [Hd1 Hp1]]].
      * split. eapply dis_rel_dis. apply Hd0. apply Hii. eapply Hclo. apply Hvv. apply Hii. apply Hp0.
      * split; assumption.
Defined.
Arguments eqpair_dom {V I} VRel IRel P Hclo.


Definition Pf (V I : Ty) (f : [I] -> [V] -> [V]) (vi : [Times V I]) := exists v', f (snd vi) v' = fst vi.

(* insert past the end of the list is a no-op (the element is dropped). *)
Lemma insert_oversize : forall (A : Set) (a : A) (t : seq A) n,
    size t < n -> insert n a t = t.
Proof.
  intros A a t. elim: t => [|x t IH] n.
  - destruct n; [done|]. simpl. done.
  - destruct n; [done|]. simpl. intro Hsz. rewrite IH; [done|]. exact Hsz.
Qed.

(* present-case extractor: if the inserted inl-element really lands in the list
   (n <= size), lthread records that its state w is rel-related to an f-computed
   state.  This is the seed for Pf via the closure Hclo. *)
Lemma lthread_insert_rel : forall (V I O : Ty) (VRel : myrel [V])
    (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l w i
    (T : seq ([Times V I] + [Times V O])) v n,
    n <= size T ->
    lthread VRel f g l v (insert n (inl (w, i)) T) ->
    exists v', rel VRel l w (f i v').
Proof.
  intros V I O VRel f g l w i T v n. move: T v.
  elim: n => [|n IH] T v.
  - intros _ Hlt. simpl in Hlt. destruct Hlt as [Hr _]. exists v. exact Hr.
  - destruct T as [|a T']; simpl.
    + intro H. discriminate.
    + intro Hle. destruct a as [wo|wo]; simpl; intros [Hr Hlt']; eapply (IH T' _ Hle Hlt').
Qed.

Lemma projIl_size : forall (V I O : Ty) (T : seq ([Times V I] + [Times V O])),
    size (projIl T) = size T.
Proof. intros V I O. elim => //= x t ->. done. Qed.

Lemma projOl_size : forall (V I O : Ty) (T : seq ([Times V I] + [Times V O])),
    size (projOl T) = size T.
Proof. intros V I O. elim => //= x t ->. done. Qed.

(* The converse machinery, specialised to the domain-restricted relation         *)
(* (eqpair_dom VRel IRel (Pf f) Hclo).  Identical to the library `sta_conv`       *)
(* except the input-case rel-witness uses eqpair_dom's left (related) branch.     *)
Lemma sta_conv' : forall (I O V : Ty) (VRel : myrel [V]) (IRel : myrel [I]) (ORel : myrel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V])
    (Hclo : forall l x y, rel VRel l x.1 y.1 -> rel IRel l x.2 y.2 -> Pf f x -> Pf f y)
    l L (p : Proc (Times V I) O) v,
    fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f ->
    NI (eqpair_dom VRel IRel (Pf f) Hclo) ORel p ->
    Trace ORel l (projOl L) p -> lthread VRel f g l v L ->
    Trace (eqpair VRel ORel) l (projIl L) (sta f g v p).
Proof.
  intros I O V VRel IRel ORel f g Hclo l L. elim: L => [|a L' IH] p v Hg Hf HNI HT Hl.
  - simpl. con.
  - destruct a as [[w x]|[w x]]; simpl in *; destruct Hl as [Hw Hl].
    + move: (HNI l) => [Hrel _].
      have Hsw : rel (eqpair_dom VRel IRel (Pf f) Hclo) l (w,x) (f x v, x).
      { left. split; [apply Hw | apply rel_refl]. }
      apply (Hrel (projOl L') (w,x) (f x v, x) 0 Hsw) in HT.
      simpl in HT. inv HT.
      econ. econ. reflexivity. apply H1.
      eapply IH. apply Hg. apply Hf. eapply NI_reduceI. apply HNI. apply H1. apply H3. apply Hl.
    + inv HT.
      econ. econ. reflexivity. apply H1.
      split. eapply rel_trans. eapply Hg. apply H2. apply rel_refl. apply rel_sym. apply Hw. apply H2.
      eapply IH. apply Hg. apply Hf. eapply NI_reduceO. apply HNI. apply H1. apply H4.
      eapply lthread_stable. apply Hf. apply Hg. 2: apply Hl. eapply Hg. apply rel_sym. apply H2. apply rel_refl.
Qed.

Lemma sta_NI' : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O])
    (Hclo : forall l x y, rel VRel l x.1 y.1 -> rel IRel l x.2 y.2 -> Pf f x -> Pf f y),
    fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f -> f_EP IRel VRel f ->
    NI (eqpair_dom VRel IRel (Pf f) Hclo) ORel p ->
    NI IRel (eqpair VRel ORel) (sta f g v p).
Proof.
  intros I O V p f g v IRel VRel ORel Hclo Hg Hf Hep Hp. rewrite /NI /NI_l. intros l. ssa.
  - (* clause 1 (rel) *)
    intros t i i' n Hii HT.
    eapply sta_proj_lthread in HT. 2: apply Hf. 2: apply Hg.
    move: HT => [T] [Heq] [Htp] Hlt.
    symmetry in Heq. move/(projIl_insert_inv v) : Heq => [w] [T''] [HT' Ht''].
    subst T. subst t.
    rewrite projOl_insert in Htp. simpl in Htp.
    move: (Hp l) => [Hrel _].
    eapply (Hrel (projOl T'') (w,i) (w,i') n) in Htp;
      last by (left; split; [apply rel_refl | apply Hii]).
    have Hl' : lthread VRel f g l v (insert n (inl (w, i')) T'').
    { eapply lthread_swap. apply Hf. apply Hg. apply Hii. apply Hlt. }
    have Hfin : Trace (eqpair VRel ORel) l (projIl (insert n (inl (w, i')) T'')) (sta f g v p).
    { eapply sta_conv'. apply Hg. apply Hf. apply Hp. rewrite projOl_insert. simpl. apply Htp. apply Hl'. }
    rewrite projIl_insert in Hfin. simpl in Hfin. apply Hfin.
  - (* clause 2 (insert disclosed) *)
    intros t i n Hdi HT.
    eapply sta_proj_lthread in HT. 2: apply Hf. 2: apply Hg.
    move: HT => [T] [Heq [Htp Hlt]]. subst t.
    case: (leqP n (size T)) => Hsz.
    + (* present: the inserted element really lands in the list *)
      have [w Hw] : exists w, lthread VRel f g l v (insert n (inl (w, i)) T)
        by eapply lthread_insert_dis; eauto.
      have HPf : Pf f (w, i).
      { have [v' Hr] : exists v', rel VRel l w (f i v') by eapply lthread_insert_rel; [exact Hsz | exact Hw].
        eapply (Hclo l (f i v', i) (w, i)); [apply rel_sym; apply Hr | apply rel_refl | by exists v']. }
      have -> : insert n (inl i) (projIl T) = projIl (insert n (inl (w, i)) T) by rewrite projIl_insert.
      eapply sta_conv'. apply Hg. apply Hf. apply Hp. 2: exact Hw.
      rewrite projOl_insert. simpl.
      move: (Hp l) => [_ [Hins _]]. eapply Hins. 2: apply Htp.
      simpl. split; [apply Hdi | apply HPf].
    + (* absent: insert past the end is a no-op, the inserted element is dropped *)
      have -> : insert n (inl i) (projIl T) = projIl T
        by apply insert_oversize; rewrite projIl_size; exact Hsz.
      eapply sta_conv'. apply Hg. apply Hf. apply Hp. apply Htp. apply Hlt.
  - (* clause 3 (remove disclosed) *)
    intros t i n Hdi HT.
    eapply sta_proj_lthread in HT. 2: apply Hf. 2: apply Hg.
    move: HT => [T] [Heq [Htp Hlt]].
    symmetry in Heq. move/(projIl_insert_inv v) : Heq => [w] [T''] [HT' Ht''].
    subst T. subst t.
    have Hl' : lthread VRel f g l v T''.
    { eapply lthread_remove_dis; eauto. }
    eapply sta_conv'. apply Hg. apply Hf. apply Hp. 2: exact Hl'.
    rewrite projOl_insert in Htp. simpl in Htp.
    case: (leqP n (size T'')) => Hsz.
    + (* present: the recorded element really is in the list *)
      have HPf : Pf f (w, i).
      { have [v' Hr] : exists v', rel VRel l w (f i v') by eapply lthread_insert_rel; [exact Hsz | exact Hlt].
        eapply (Hclo l (f i v', i) (w, i)); [apply rel_sym; apply Hr | apply rel_refl | by exists v']. }
      move: (Hp l) => [_ [_ Hrem]]. eapply Hrem; [|apply Htp].
      simpl. split; [apply Hdi | apply HPf].
    + (* absent: the recorded element was dropped, removal is a no-op *)
      rewrite insert_oversize in Htp; [exact Htp | rewrite projOl_size; exact Hsz].
Qed.


(* The closure that discharges eqpair_dom's Hclo for the bool predicate          *)
(* (fun bi => bi.1 = false), purely from `aware BRel true`.  A `false`-state and  *)
(* a non-`false`-state are never related, so the disclosed set stays a full       *)
(* rel-equivalence class.                                                         *)
Lemma aware_false_closure : forall (I : Ty) (IRel : myrel [I]) (BRel : myrel [Bool]),
    (forall l, aware BRel true l) ->
    forall l (x y : [Times Bool I]),
      rel BRel l x.1 y.1 -> rel IRel l x.2 y.2 -> x.1 = false -> y.1 = false.
Proof.
  intros I IRel BRel Haware l x y Hb Hi Hf.
  destruct (y.1) eqn:E; [|reflexivity].
  rewrite Hf in Hb. apply rel_sym in Hb.
  destruct (Haware l _ Hb) as [Hc _]. discriminate Hc.
Qed.
Arguments aware_false_closure {I} IRel {BRel} _.


Lemma swi_trace_insert_conv_false : forall (I O : Ty) (ORel : myrel [O]) (BRel : myrel [Bool]) l b t t_p n (i : bool * [I]),
    i.1 = false ->
    SwiTrace ORel BRel l b t t_p ->
    exists n', SwiTrace ORel BRel l b (insert n (inl i) t) (insert n' (inl i.2) t_p).
Proof.
  intros I O ORel BRel l b t t_p n [b_in i_in] Hi1 Hswi.
  simpl in Hi1. subst b_in.
  elim: t b t_p n Hswi => [| a t IH] b t_p n Hswi.
  - inv Hswi. destruct n; simpl.
    + exists 0. repeat constructor.
    + exists 1. constructor.
  - destruct n; simpl.
    + exists 0. econstructor. rewrite xorFalse. exact Hswi.
    + inv Hswi.
      * simpl. destruct (IH _ _ n H3) as [n' Hswi'].
        exists n'.+1. constructor. exact Hswi'.
      * simpl. destruct (IH _ _ n H4) as [n' Hswi'].
        exists n'. eapply ST2_false; eauto.
      * simpl. destruct (IH _ _ n H4) as [n' Hswi'].
        exists n'.+1. eapply ST2_true; eauto.
Qed.


(* swi in the eqpair_dom shape: the input base is right-keyed BRel/IRel (the shape *)
(* sta/map produce), and the bool constraint lives in the predicate.              *)
Lemma swi_NI' : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (BRel : myrel [Bool])
    (p : Proc I (Times Bool O)) (b : bool) (Haware : forall l, aware BRel true l),
    NI IRel (eqpair_LR BRel ORel) p ->
    NI (eqpair_dom BRel IRel (fun bi => bi.1 = false) (aware_false_closure IRel Haware))
       (eqmaybe_swi ORel BRel) (swi b p).
Proof.
  intros I O IRel ORel BRel p b Haware HNI l.
  split; [| split].
  - intros t [bi val_i] [bi' val_i'] n Hrel Htr.
    have Heq_b: bi = bi'.
    { destruct Hrel as [[Hb _] | [[_ H1] [_ H2]]].
      + destruct bi, bi'; auto.
        * move: (Haware l false Hb) => [H_false _]. done.
        * move: (equiv BRel l) => [? Hsym ?].
          have Hsym_rel := Hsym _ _ Hb.
          move: (Haware l false Hsym_rel) => [H_false _]. done.
      + move: H1 H2 => /= H1 H2. rewrite H1 H2. reflexivity. }
    subst bi'.
    apply swi_trace in Htr as [t_p [Htr_p Hswi_tr]].
    have [n' [t_p' [Ht_p' Hswi_tr']]]: exists n' t_p', t_p = insert n' (inl val_i) t_p' /\ SwiTrace ORel BRel l b (insert n (inl (bi, val_i')) t) (insert n' (inl val_i') t_p').
    { eapply (swi_trace_swap (I:=I) (O:=O) (ORel:=ORel) (BRel:=BRel) (l:=l) (b:=b) (t:=t) (t_p:=t_p) (n:=n) (i:=(bi, val_i)) (i':=(bi, val_i'))); auto. }
    subst t_p.
    move: (HNI l) => [H_NI_1 [H_NI_2 H_NI_3]].
    have Htr_p': Trace (eqpair_LR BRel ORel) l (insert n' (inl val_i') t_p') p.
    { destruct Hrel as [[_ Hrel_i] | [[Hdis_i _] [Hdis_i' _]]].
      + eapply H_NI_1; [exact Hrel_i | exact Htr_p].
      + eapply H_NI_2; [exact Hdis_i' |]. eapply H_NI_3; [exact Hdis_i | exact Htr_p]. }
    eapply swi_conv; [apply Haware | apply Htr_p' | apply Hswi_tr'].
  - intros t [bi val_i] n Hdis Htr.
    simpl in Hdis. destruct Hdis as [Hdis_i Heq_b].
    apply swi_trace in Htr as [t_p [Htr_p Hswi_tr]].
    have [n' Hswi_tr']: exists n', SwiTrace ORel BRel l b (insert n (inl (bi, val_i)) t) (insert n' (inl val_i) t_p).
    { eapply swi_trace_insert_conv_false; [exact Heq_b | exact Hswi_tr]. }
    move: (HNI l) => [_ [H_NI_2 _]].
    have Htr_p': Trace (eqpair_LR BRel ORel) l (insert n' (inl val_i) t_p) p.
    { eapply H_NI_2; [exact Hdis_i | exact Htr_p]. }
    eapply swi_conv; [apply Haware | apply Htr_p' | apply Hswi_tr'].
  - intros t [bi val_i] n Hdis Htr.
    simpl in Hdis. destruct Hdis as [Hdis_i Heq_b].
    apply swi_trace in Htr as [t_p [Htr_p Hswi_tr]].
    move: Hswi_tr. rewrite Heq_b => Hswi_tr.
    have [n' [t_p' [Ht_p' Hswi_tr']]]: exists n' t_p', t_p = insert n' (inl val_i) t_p' /\ SwiTrace ORel BRel l b t t_p'.
    { eapply (swi_trace_insert (I:=I) (O:=O) (ORel:=ORel) (BRel:=BRel) (l:=l) (b:=b) (t:=t) (t':=t_p) (n:=n) (i:=(false, val_i))); [reflexivity | exact Hswi_tr]. }
    subst t_p.
    move: (HNI l) => [_ [_ H_NI_3]].
    have Htr_p': Trace (eqpair_LR BRel ORel) l t_p' p.
    { eapply H_NI_3; [exact Hdis_i | exact Htr_p]. }
    eapply swi_conv; [apply Haware | apply Htr_p' | apply Hswi_tr'].
Qed.


(* Map-congruence for eqpair_dom (keystone of the threading): a value map h that  *)
(* is NI on the V-component and carries the predicate P into Q lifts to an f_NI    *)
(* (and f_PU) between the two domain-restricted relations, so map_NI can thread    *)
(* eqpair_dom VRel I (Pf f) (from sta) to eqpair_dom BRel I (bool=false) (for swi). *)
Lemma eqpair_dom_f_NI : forall (V B I : Ty) (VRel : myrel [V]) (BRel : myrel [B]) (IRel : myrel [I])
    (P : [Times V I] -> Prop) (Q : [Times B I] -> Prop) (h : [V] -> [B])
    (HclP : forall l x y, rel VRel l x.1 y.1 -> rel IRel l x.2 y.2 -> P x -> P y)
    (HclQ : forall l x y, rel BRel l x.1 y.1 -> rel IRel l x.2 y.2 -> Q x -> Q y),
    f_NI VRel BRel h ->
    (forall x : [Times V I], P x -> Q (h x.1, x.2)) ->
    f_NI (eqpair_dom VRel IRel P HclP) (eqpair_dom BRel IRel Q HclQ)
         (fun x => (h x.1, x.2)).
Proof.
  intros V B I VRel BRel IRel P Q h HclP HclQ Hh HPQ.
  intros l x y [[Hv Hi]|[[Hdx Hpx][Hdy Hpy]]].
  - left. split; [apply Hh; exact Hv | exact Hi].
  - right. split; split; simpl.
    + exact Hdx.
    + apply HPQ; exact Hpx.
    + exact Hdy.
    + apply HPQ; exact Hpy.
Qed.

Lemma eqpair_dom_f_PU : forall (V B I : Ty) (VRel : myrel [V]) (BRel : myrel [B]) (IRel : myrel [I])
    (P : [Times V I] -> Prop) (Q : [Times B I] -> Prop) (h : [V] -> [B])
    (HclP : forall l x y, rel VRel l x.1 y.1 -> rel IRel l x.2 y.2 -> P x -> P y)
    (HclQ : forall l x y, rel BRel l x.1 y.1 -> rel IRel l x.2 y.2 -> Q x -> Q y),
    (forall x : [Times V I], P x -> Q (h x.1, x.2)) ->
    f_PU (eqpair_dom VRel IRel P HclP) (eqpair_dom BRel IRel Q HclQ)
         (fun x => (h x.1, x.2)).
Proof.
  intros V B I VRel BRel IRel P Q h HclP HclQ HPQ.
  intros l x [Hd Hp]. split; simpl; [exact Hd | apply HPQ; exact Hp].
Qed.
