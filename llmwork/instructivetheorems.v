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

Require Export NonInterference.llmwork.model.

Lemma out_NI : forall I O (IRel : myrel [I]) (ORel : myrel [O]) (o : [O]), NI IRel ORel (out o).
Proof.
  intros. rewrite /NI.
  move=>l. rewrite /NI_l. ssa.
  - ssa. elim: t n H0.
    + ssa. de n; repeat econ.
    + ssa. de n.
      * econ. econ. inv H1. match_dd. done.
      * inv H1.
        { econ. econ. match_dd. eauto. }
        { econ. econ. match_dd. done. match_dd. eauto. }
  - ssa. elim: t n H0.
    + ssa. de n; repeat econ.
    + ssa. inv H1. match_dd.
      * de n.
        { econ. econ. done. }
        { econ. econ. eauto. }
      * de n.
        { econ. econ. done. }
        { econ. econ. match_dd. done. match_dd. eauto. }
  - intros t i n Hd. move: t. elim: n => [|n IH].
    + intros t HT. simpl in HT. inv HT. match_dd. apply H3.
    + intros t HT. destruct t as [|a t]; simpl in HT.
      * apply HT.
      * inv HT.
        { match_dd. econ. econ. eapply IH. apply H3. }
        { match_dd. econ. econ. apply H2. eapply IH. apply H4. }
Qed.


Inductive MapTrace (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (ORel : myrel [O']) (l : level) : seq ([I] + [O']) -> seq ([I'] + [O]) -> Prop  :=
| MT0 : MapTrace f g ORel l nil nil
| MT1 i t t' : (*reduceI p (f i) p' -> *) MapTrace f g ORel l t t' -> MapTrace f g ORel l ((inl i)::t) ((inl (f i))::t')
| MT2 o o' t t' : rel ORel l (g o) o' -> MapTrace f g ORel l t t' -> MapTrace f g ORel l ((inr o')::t) ((inr o)::t').

Lemma map_trace : forall (I I' O O' : Ty) (p : Proc I' O) (ORel : myrel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t,
    Trace ORel l t (map f g p) -> exists t', forall ORel', Trace ORel' l t' p /\ MapTrace f g ORel l t t'.
Proof.
  intros. elim: t p H. ssa. exists nil. ssa. con.
  ssa. inv H0. match_dd. eapply H in H5. ssa.
  econ. intros.
  move: (H1 ORel'). case. intros. con.
  instantiate (1:= (inl (f i))::_). econ. eauto. eauto. econ. eauto. 

  match_dd.
  apply H in H6. ssa.
  econ. intros.
  move: (H1 ORel'). case. intros.
  con. 2: {  econ. eauto. eauto. }
     econ. eauto. done. done.
Qed.  

Lemma map_trace_insert : forall (I I' O O' : Ty) (ORel' : myrel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n i,
    MapTrace f g ORel' l (insert n (inl i) t) t' -> exists t'', t' = insert n (inl (f i)) t''.
Proof.
  ssa.
  elim: t n t' H. ssa.
  de n. ssa. inv H. econ. econ.
  inv H. exists nil. done.
  ssa. de n. inv H0. econ. econ.
  inv H0.
  apply H in H4. ssa. rewrite H1.
  econ. instantiate (1:= cons _ _). simpl. econ.
  apply H in H5. ssa. rewrite H1.
  econ. instantiate (1:= cons _ _). simpl. econ.
Qed.

Lemma map_trace_insert2 : forall (I I' O O' : Ty) (ORel' : myrel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n x y,
    MapTrace f g ORel' l (insert n x t) (insert n y t') -> MapTrace f g ORel' l t t'.
Proof.
  intros. elim : t n t' H.
  case. ssa. inv H. inv H1. done. inv H5. done.
  ssa. de t'. inv H.

  ssa. de n. inv H0. inv H2.
  con. done.
  con. done. done. inv H6. con. done. con. done. done.
  de t'. inv H0. inv H0.
  econ. eauto.
  econ. done. eauto.
Qed.

Lemma map_trace_insert3 : forall (I I' O O' : Ty) (ORel' : myrel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n i,
    MapTrace f g ORel' l t t' ->  MapTrace f g ORel' l (insert n (inl i) t) (insert n (inl (f i)) t').
Proof.
  intros. elim : t n t' H.
  case. ssa. inv H. econ. done.
  ssa. de t'. inv H.

  ssa. inv H0. de n.  econ. econ. done.
  econ. eauto. de n. econ. econ. done. done.
  econ. done. eauto.
Qed.

Lemma map_trace_remove3 : forall (I I' O O' : Ty) (ORel' : myrel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n,
    MapTrace f g ORel' l t t' ->  MapTrace f g ORel' l (remove n t) (remove n t').
Proof.
  intros. elim : t n t' H.
  case. ssa. inv H. econ. 
  ssa. de t'. inv H.

  ssa. inv H0. de n.  
  econ. eauto. de n. econ. done. eauto.
Qed.

Lemma map_trace_insert4 : forall (I I' O O' : Ty) (ORel' : myrel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n (i i' : [I]),
    MapTrace f g ORel' l (insert n (inl i) t) (insert n (inl (f i)) t') ->  MapTrace f g ORel' l (insert n (inl i') t) (insert n (inl (f i')) t').
Proof.
  intros. apply map_trace_insert3. eapply map_trace_insert2. eauto.
Qed.


Lemma map_NI : forall (I I' O O' : Ty) (p : Proc I' O) (f : [I] -> [I']) (g : [O] -> [O']) (IRel : myrel [I]) (IRel' : myrel [I']) (ORel : myrel [O]) (ORel' : myrel [O']),
    f_NI IRel IRel' f -> f_PU IRel IRel' f -> f_NI ORel ORel' g ->
    NI IRel' ORel p ->     
    NI IRel ORel' (map f g p).
Proof.
  intros.
  move: p H2. rewrite /NI /NI_l.
  ssa. move: (H2 l). ssa. clear H2 H6.
  - eapply map_trace in H5. ssa.
    move: (H2 ORel). case. intros.
    apply map_trace_insert in b as b'. ssa. subst. clear H2.
    eapply H3 in a. 2: apply H. 2:apply H4.
    eapply map_trace_insert4 in b.
    move: b. instantiate (1:= i'). move=>aa. clear H3 H7. move: aa p a.
    elim.
    + done.
    + ssa. inv a. econ. econ. eauto. eauto. eauto.
    + ssa. inv a. econ. econ. econ. eauto. eauto. eauto.
  - move: (H2 l). case. move=>_. case. intros. clear H2 b.
    have: dis IRel' l (f i). { rewrite /f_PU in H0. apply H0. done. }
    intros.
    apply map_trace in H4. ssa.
    move: (H4 ORel).   ssa.
    eapply a in H2. 2:eauto.
    move: H2. instantiate (1:= n).
    clear H4. clear a.
    clear H5. move: H6 p.
    move/map_trace_insert3.
    move/(_ n i). elim.
    + ssa.
    + ssa. inv H5. econ. econ. eauto. eauto. eauto.
    + ssa. inv H6. econ. econ. eauto. eauto. eauto. eauto.
  - intros t i n Hd HT.
    apply map_trace in HT. move: HT => [t'] Hb.
    move: (Hb ORel) => [Htp Hmt].
    apply map_trace_insert in Hmt as Hmt'. move: Hmt' => [t''] Heq. subst t'.
    move: (H2 l) => [_ [_ HH]].
    have Hdfi : dis IRel' l (f i). { apply H0. apply Hd. }
    eapply HH in Htp. 2: apply Hdfi.
    eapply map_trace_insert2 in Hmt.
    clear H2 Hb HH Hdfi.
    move: p Htp. elim: Hmt.
    + ssa.
    + ssa. inv Htp. econ. econ. eauto. eauto. eauto.
    + ssa. inv Htp. econ. econ. eauto. eauto. eauto. eauto.
Qed.
