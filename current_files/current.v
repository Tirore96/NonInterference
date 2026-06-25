
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


Definition eqpair_P {I : Ty} (IRel : myrel [I]) (P : [I] -> Prop) : myrel ([I]).
  refine (@MyRel _ 
            (fun (l : level) i => dis IRel l i /\ (exists i', rel IRel l i i' /\ P i'  ))
            (fun l i0 i1 => rel IRel l i0 i1 \/
                             (dis IRel l i0 /\ (exists i', rel IRel l i0 i' /\ P i' )) /\
                             (dis IRel l i1 /\ (exists i', rel IRel l i1 i' /\ P i' ))                               
            )
            _
            _
            _
            _).
  - ssa. con. intro. ssa. intro. ssa. de H.
    intro. ssa. de H. de H0. left. eauto.
    left. eauto. de H0. eauto.
    ssa. de H0. eauto. right. ssa. eauto. eauto. eauto. eauto.
    ssa. eauto. eauto.
    ssa. con. ssa. ssa. de H2. eauto. de H2. eauto. eauto.
Defined.



Definition Pf (V I : Ty) (f : [I] -> [V] -> [V]) (vi : [Times V I]) := exists v', f (snd vi) v' = fst vi.

(* The converse machinery, specialised to the restricted relation               *)
(* (eqpair_P (eqpair_R VRel IRel) (Pf f)).  Identical to the library `sta_conv`  *)
(* except the input-case rel-witness is injected through the extra eqpair_P      *)
(* disjunct (left. left. instead of left.).                                      *)
Lemma sta_conv' : forall (I O V : Ty) (VRel : myrel [V]) (IRel : myrel [I]) (ORel : myrel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l L (p : Proc (Times V I) O) v,
    fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f ->
    NI (eqpair_P (eqpair_R VRel IRel) (Pf f)) ORel p ->
    Trace ORel l (projOl L) p -> lthread VRel f g l v L ->
    Trace (eqpair VRel ORel) l (projIl L) (sta f g v p).
Proof.
  intros I O V VRel IRel ORel f g l L. elim: L => [|a L' IH] p v Hg Hf HNI HT Hl.
  - simpl. con.
  - destruct a as [[w x]|[w x]]; simpl in *; destruct Hl as [Hw Hl].
    + move: (HNI l) => [Hrel _].
      have Hsw : rel (eqpair_P (eqpair_R VRel IRel) (Pf f)) l (w,x) (f x v, x).
      { left. left. split; [apply Hw | apply rel_refl]. }
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

Lemma sta_NI' : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O]),
    fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f -> f_EP IRel VRel f ->
    NI (eqpair_P (eqpair_R VRel IRel) (Pf f) ) ORel p ->
    NI IRel (eqpair VRel ORel) (sta f g v p).
Proof.
  intros I O V p f g v IRel VRel ORel Hg Hf Hep Hp. rewrite /NI /NI_l. intros l. ssa.
  - (* clause 1 (rel) *)
    intros t i i' n Hii HT.
    eapply sta_proj_lthread in HT. 2: apply Hf. 2: apply Hg.
    move: HT => [T] [Heq] [Htp] Hlt.
    symmetry in Heq. move/(projIl_insert_inv v) : Heq => [w] [T''] [HT' Ht''].
    subst T. subst t.
    rewrite projOl_insert in Htp. simpl in Htp.
    move: (Hp l) => [Hrel _].
    eapply (Hrel (projOl T'') (w,i) (w,i') n) in Htp;
      last by (left; left; split; [apply rel_refl | apply Hii]).
    have Hl' : lthread VRel f g l v (insert n (inl (w, i')) T'').
    { eapply lthread_swap. apply Hf. apply Hg. apply Hii. apply Hlt. }
    have Hfin : Trace (eqpair VRel ORel) l (projIl (insert n (inl (w, i')) T'')) (sta f g v p).
    { eapply sta_conv'. apply Hg. apply Hf. apply Hp. rewrite projOl_insert. simpl. apply Htp. apply Hl'. }
    rewrite projIl_insert in Hfin. simpl in Hfin. apply Hfin.
  - (* clause 2 (insert disclosed) *)
    intros t i n Hdi HT.
    eapply sta_proj_lthread in HT. 2: apply Hf. 2: apply Hg.
    move: HT => [T] [Heq [Htp Hlt]]. subst t.
    have [w Hw] : exists w, lthread VRel f g l v (insert n (inl (w, i)) T).
    { eapply lthread_insert_dis; eauto. }
    have -> : insert n (inl i) (projIl T) = projIl (insert n (inl (w, i)) T) by rewrite projIl_insert.
    eapply sta_conv'. apply Hg. apply Hf. apply Hp. 2: exact Hw.
    rewrite projOl_insert. simpl.
    move: (Hp l) => [_ [Hins _]]. eapply Hins. 2: apply Htp.
    simpl. split; [apply Hdi | exists (f i v, i); split; [right; split; apply Hdi | exists v; reflexivity]].
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
    move: (Hp l) => [_ [_ Hrem]]. eapply Hrem; [|apply Htp].
    simpl. split; [apply Hdi | exists (f i v, i); split; [right; split; apply Hdi | exists v; reflexivity]].
Qed.


Lemma collapse_test : forall (I : Ty) (IRel : myrel [I]) (BRel : myrel [Bool]) i l,
  dis IRel l i ->
  dis (eqpair_P (eqpair_R BRel IRel) (fun bi => fst bi = false)) l (true, i).
  ssa. econ. ssa. 2: { instantiate (1:= (false,_)).  simpl. done. }  simpl. right. ssa. eauto.
