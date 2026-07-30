Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import RelationClasses.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
From HB Require Import structures.
From deriving Require Import deriving.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.Classes.DecidableClass.

Import Order.TTheory.
Open Scope order_scope.

Require Export NonInterference.theories.definitions.

Lemma out_NI : forall I O (IRel : cRel [I]) (ORel : cRel [O]) (o : [O]), NI IRel ORel (out o).
Proof.
  intros. rewrite /NI.
  move=>l. rewrite /NI_l. ssa.
  ssa.
  
  elim : t n H0.
  ssa. de n. econ. econ. econ.
  ssa. de n. econ. econ. inv H1. match_dd. done.
  inv H1. econ. econ. match_dd. eauto.
  econ. econ. match_dd.  done.
  match_dd. eauto.


  ssa. elim: t n H0. ssa. de n. econ. econ. done.
  ssa. inv H1. match_dd. de n. econ. econ. done.
  econ. econ. eauto.
  de n. econ. econ. done.
  econ. econ. match_dd. done. match_dd. eauto.

  intros t i n Hd. move: t. elim: n => [|n IH].
  - intros t HT. simpl in HT. inv HT. match_dd. apply H3.
  - intros t HT. destruct t as [|a t]; simpl in HT.
    + apply HT.
    + inv HT.
      * match_dd. econ. econ. eapply IH. apply H3.
      * match_dd. econ. econ. apply H2. eapply IH. apply H4.
Qed.


Inductive MapTrace (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (ORel : cRel [O']) (l : level) : seq ([I] + [O']) -> seq ([I'] + [O]) -> Prop  :=
| MT0 : MapTrace f g ORel l nil nil
| MT1 i t t' : (*reduceI p (f i) p' -> *) MapTrace f g ORel l t t' -> MapTrace f g ORel l ((inl i)::t) ((inl (f i))::t')
| MT2 o o' t t' : rel ORel l (g o) o' -> MapTrace f g ORel l t t' -> MapTrace f g ORel l ((inr o')::t) ((inr o)::t').

Lemma map_trace : forall (I I' O O' : Ty) (p : Proc I' O) (ORel : cRel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t,
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

Lemma map_trace_insert : forall (I I' O O' : Ty) (ORel' : cRel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n i,
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

Lemma map_trace_insert2 : forall (I I' O O' : Ty) (ORel' : cRel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n x y,
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

Lemma map_trace_insert3 : forall (I I' O O' : Ty) (ORel' : cRel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n i,
    MapTrace f g ORel' l t t' ->  MapTrace f g ORel' l (insert n (inl i) t) (insert n (inl (f i)) t').
Proof.
  intros. elim : t n t' H.
  case. ssa. inv H. econ. done.
  ssa. de t'. inv H.

  ssa. inv H0. de n.  econ. econ. done.
  econ. eauto. de n. econ. econ. done. done.
  econ. done. eauto.
Qed.

Lemma map_trace_remove3 : forall (I I' O O' : Ty) (ORel' : cRel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n,
    MapTrace f g ORel' l t t' ->  MapTrace f g ORel' l (remove n t) (remove n t').
Proof.
  intros. elim : t n t' H.
  case. ssa. inv H. econ. 
  ssa. de t'. inv H.

  ssa. inv H0. de n.  
  econ. eauto. de n. econ. done. eauto.
Qed.

Lemma map_trace_insert4 : forall (I I' O O' : Ty) (ORel' : cRel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' n (i i' : [I]),
    MapTrace f g ORel' l (insert n (inl i) t) (insert n (inl (f i)) t') ->  MapTrace f g ORel' l (insert n (inl i') t) (insert n (inl (f i')) t').
Proof.
  intros. apply map_trace_insert3. eapply map_trace_insert2. eauto.
Qed.


Lemma map_NI : forall (I I' O O' : Ty) (p : Proc I' O) (f : [I] -> [I']) (g : [O] -> [O']) (IRel : cRel [I]) (IRel' : cRel [I']) (ORel : cRel [O]) (ORel' : cRel [O']),
    f_NI IRel IRel' f -> f_PU IRel IRel' f -> f_NI ORel ORel' g ->
    NI IRel' ORel p ->     
    NI IRel ORel' (map f g p).
Proof.
  intros.
  move: p H2. rewrite /NI /NI_l.
  ssa. move: (H2 l). ssa. clear H2 H6.
  eapply map_trace in H5. ssa.
  move: (H2 ORel). case. intros.

  apply map_trace_insert in b as b'. ssa. subst. clear H2.
  eapply H3 in a. 2: apply H. 2:apply H4.
  eapply map_trace_insert4 in b.
  move: b. instantiate (1:= i'). move=>aa. clear H3 H7. move: aa p a.
  elim. done.
  ssa. inv a. econ. econ. eauto. eauto. eauto.

  ssa. inv a. econ. econ. econ. eauto. eauto. eauto.

  move: (H2 l). case. move=>_. case. intros. clear H2 b.
  have: dis IRel' l (f i). rewrite /f_PU in H0. apply H0. done.
  intros.
  apply map_trace in H4. ssa.
  move: (H4 ORel).   ssa.
  eapply a in H2. 2:eauto.
  move: H2. instantiate (1:= n).
  clear H4. clear a.
  clear H5. move: H6 p.
  move/map_trace_insert3.
  move/(_ n i). elim. ssa.
  ssa. inv H5. econ. econ. eauto. eauto. eauto.
  ssa. inv H6. econ. econ. eauto. eauto. eauto. eauto.


  intros t i n Hd HT.
  apply map_trace in HT. move: HT => [t'] Hb.
  move: (Hb ORel) => [Htp Hmt].
  apply map_trace_insert in Hmt as Hmt'. move: Hmt' => [t''] Heq. subst t'.
  move: (H2 l) => [_ [_ HH]].
  have Hdfi : dis IRel' l (f i). { apply H0. apply Hd. }
  eapply HH in Htp. 2: apply Hdfi.
  eapply map_trace_insert2 in Hmt.
  clear H2 Hb HH Hdfi.
  move: p Htp. elim: Hmt.
  - ssa.
  - ssa. inv Htp. econ. econ. eauto. eauto. eauto.
  - ssa. inv Htp. econ. econ. eauto. eauto. eauto. eauto.
Qed.


(*The rest of this file is generated with claude*)


(* ============================================================== *)
(* NEW APPROACH: one state-threaded list, two projections.        *)
(*                                                                *)
(* An element of the threaded list carries the state on whichever *)
(* side needs it:                                                 *)
(*   inl (w,i) : an input step  -- w is the post-input state      *)
(*               (= f i v), i the input.                          *)
(*   inr (w,o) : an output step -- w is the post-output state     *)
(*               (= g o v), o the (observed) output.              *)
(*                                                                *)
(*   projI drops the state from INPUTS  -> the sta-trace          *)
(*         (over [I] + [Times V O]).                              *)
(*   projO drops the state from OUTPUTS -> the p-trace            *)
(*         (over [Times V I] + [O]).                              *)
(* ============================================================== *)

Definition projI (V I O : Ty) (x : [Times V I] + [Times V O]) : [I] + [Times V O] :=
  match x with
  | inl vi => inl (snd vi)
  | inr vo => inr vo
  end.

Definition projO (V I O : Ty) (x : [Times V I] + [Times V O]) : [Times V I] + [O] :=
  match x with
  | inl vi => inl vi
  | inr vo => inr (snd vo)
  end.

(* list-level projections (avoid the name clash with the Proc constructor map) *)
Fixpoint projIl (V I O : Ty) (t : seq ([Times V I] + [Times V O])) : seq ([I] + [Times V O]) :=
  match t with
  | nil => nil
  | x :: t' => projI x :: projIl t'
  end.

Fixpoint projOl (V I O : Ty) (t : seq ([Times V I] + [Times V O])) : seq ([Times V I] + [O]) :=
  match t with
  | nil => nil
  | x :: t' => projO x :: projOl t'
  end.

(* Forward: any trace of (sta f g v p) is the projIl-image of a threaded      *)
(* list whose projOl-image is a trace of p.                                   *)
Lemma sta_proj : forall (I O V : Ty) (p : Proc (Times V I) O) (VRel : cRel [V]) (ORel : cRel [O]) (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) l v ts,
    Trace (eqpair VRel ORel) l ts (sta f g v p) ->
    exists t, ts = projIl t /\ Trace ORel l (projOl t) p.
Proof.
  intros I O V p VRel ORel f g l v ts. move: p v. elim: ts.
  - intros p v HT. exists nil. ssa.
  - intros a ts IH p v HT. inv HT.
    + match_dd. move: (IH _ _ H3) => [t] [Hpi] Hpo.
      exists (inl (f i v, i) :: t). split.
      * simpl. rewrite Hpi. done.
      * simpl. econ. eauto. apply Hpo.
    + match_dd. move: (IH _ _ H4) => [t] [Hpi] Hpo.
      exists (inr o :: t). split.
      * simpl. rewrite Hpi. done.
      * simpl. econ. eauto. 2: apply Hpo. move: H2 => [_ HO]. apply HO.
Qed.

(* Specialisation to the NI call-site: the composite trace insert n (inl i) t  *)
(* is EXACTLY projIl T, and projOl T is a trace of p, for one shared list T.    *)
Lemma sta_proj_insert : forall (I O V : Ty) (p : Proc (Times V I) O) (VRel : cRel [V]) (ORel : cRel [O]) (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) l v n i t,
    Trace (eqpair VRel ORel) l (insert n (inl i) t) (sta f g v p) ->
    exists T, insert n (inl i) t = projIl T /\ Trace ORel l (projOl T) p.
Proof. intros. eapply sta_proj. apply H. Qed.

(* A list is "threaded" from v when each stored state is the f/g-update of    *)
(* the previous one, using the recorded input/output in that element.         *)
Fixpoint threaded (V I O : Ty) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) (v : [V]) (t : seq ([Times V I] + [Times V O])) : Prop :=
  match t with
  | nil => True
  | inl wi :: t' => fst wi = f (snd wi) v /\ threaded f g (f (snd wi) v) t'
  | inr wo :: t' => fst wo = g (snd wo) v /\ threaded f g (g (snd wo) v) t'
  end.

(* Converse direction.  The INPUT case goes through (reduceI is exact-enough).  *)
(* The OUTPUT case does NOT: rebuilding the sta-step uses p's ACTUAL output o', *)
(* so the continuation is (sta f g (g o' v) p'), but `threaded` only provides   *)
(* the suffix threaded from (g w2 v) where w2 is the RECORDED output, and       *)
(* o' <> w2 (only rel ORel o' w2, since Trace records outputs up to rel).  The  *)
(* concrete stuck goal:                                                         *)
(*   H2  : rel ORel l o' w2                                                     *)
(*   Hth : threaded f g (g w2 v) t                                             *)
(*   |-  Trace (eqpair VRel ORel) l (projIl t) (sta f g (g o' v) p')           *)
(* This is the SAME obstacle as before (NI not closed under reduceO): the       *)
(* forward projection yields a *loose* list, the converse needs an *exactly*    *)
(* threaded one, and bridging them needs NI of a reduceO-reduct.                *)


(* ---- NI is closed under reduction (both reduceI and reduceO). ----          *)
(* CORRECTION: reduceO IS deterministic (the earlier "non-determinism" was an   *)
(* artifact of stating determinism with the output fixed; the full statement    *)
(* below holds, and the map case closes because the subprocess has a unique     *)
(* output).  Hence NI_reduceO holds, which is exactly what the rebuild needs.   *)
Lemma reduceI_det : forall I O (p : Proc I O) i p1, reduceI p i p1 -> forall p2, reduceI p i p2 -> p1 = p2.
Proof.
  intros I O p i p1 H. elim: H; intros; match_dd; subst; f_equal; eauto.
Qed.

Lemma reduceO_det : forall I O (p : Proc I O) o1 p1, reduceO p o1 p1 -> forall o2 p2, reduceO p o2 p2 -> o1 = o2 /\ p1 = p2.
Proof.
  intros I O p o1 p1 H. elim: H; intros; match_dd;
  repeat (match goal with
          | [ IH : forall o2 p2, reduceO ?q o2 p2 -> _, HH : reduceO ?q _ _ |- _ ] =>
              apply IH in HH; destruct HH
          | [ E : (_, _) = (_, _) |- _ ] => inversion E; clear E
          | [ H1 : reduceI ?q ?i ?a, H2 : reduceI ?q ?i ?b |- _ ] =>
              assert (a = b) by (eapply reduceI_det; eassumption); clear H2
          end; subst);
  split; reflexivity.
Qed.

Lemma NI_reduceI : forall I O (IRel : cRel [I]) (ORel : cRel [O]) (p p' : Proc I O) i,
    NI IRel ORel p -> reduceI p i p' -> NI IRel ORel p'.
Proof.
  intros I O IRel ORel p p' i HNI Hred l.
  move: (HNI l) => [Hrel [Hins Hrem]]. split;[|split].
  - intros t a a' n Hr HT.
    have HTp2: Trace ORel l (insert n.+1 (inl a) (inl i :: t)) p. econ. apply Hred. apply HT.
    apply (Hrel (inl i :: t) a a' n.+1 Hr) in HTp2.
    simpl in HTp2. inv HTp2. eapply reduceI_det in Hred. 2: apply H1. subst. apply H3.
  - intros t a n Hd HT.
    have HTp: Trace ORel l (inl i :: t) p. econ. apply Hred. apply HT.
    apply (Hins (inl i :: t) a n.+1 Hd) in HTp.
    simpl in HTp. inv HTp. eapply reduceI_det in Hred. 2: apply H1. subst. apply H3.
  - intros t a n Hd HT.
    have HTp: Trace ORel l (insert n.+1 (inl a) (inl i :: t)) p. simpl. econ. apply Hred. apply HT.
    apply (Hrem (inl i :: t) a n.+1 Hd) in HTp.
    simpl in HTp. inv HTp. eapply reduceI_det in Hred. 2: apply H1. subst. apply H3.
Qed.

Lemma NI_reduceO : forall I O (IRel : cRel [I]) (ORel : cRel [O]) (p p' : Proc I O) o,
    NI IRel ORel p -> reduceO p o p' -> NI IRel ORel p'.
Proof.
  intros I O IRel ORel p p' o HNI Hred l.
  move: (HNI l) => [Hrel [Hins Hrem]]. split;[|split].
  - intros t a a' n Hr HT.
    have HTp: Trace ORel l (inr o :: insert n (inl a) t) p. econ. apply Hred. apply rel_refl. apply HT.
    apply (Hrel (inr o :: t) a a' n.+1 Hr) in HTp.
    simpl in HTp. inv HTp. eapply reduceO_det in Hred. 2: apply H1. destruct Hred. subst. assumption.
  - intros t a n Hd HT.
    have HTp: Trace ORel l (inr o :: t) p. econ. apply Hred. apply rel_refl. apply HT.
    apply (Hins (inr o :: t) a n.+1 Hd) in HTp.
    simpl in HTp. inv HTp. eapply reduceO_det in Hred. 2: apply H1. destruct Hred. subst. assumption.
  - intros t a n Hd HT.
    have HTp: Trace ORel l (inr o :: insert n (inl a) t) p. econ. apply Hred. apply rel_refl. apply HT.
    apply (Hrem (inr o :: t) a n.+1 Hd) in HTp.
    simpl in HTp. inv HTp. eapply reduceO_det in Hred. 2: apply H1. destruct Hred. subst. assumption.
Qed.

(* Structural helpers for the NI proof (both straightforward, left Admitted). *)
Lemma projIl_insert_inv : forall (V I O : Ty) (v : [V]) (T : seq ([Times V I] + [Times V O])) n i t,
    projIl T = insert n (inl i) t -> exists w T'', T = insert n (inl (w, i)) T'' /\ projIl T'' = t.
Proof.
  intros V I O v T. elim: T => [| a T' IH] n i t H.
  - simpl in H. destruct n; simpl in H.
    + discriminate.
    + destruct t; try discriminate.
      exists v, nil. split; done.
  - destruct n.
    + simpl in H. inversion H. subst.
      destruct a as [[w i0] | vo].
      * simpl in H1. inversion H1. subst.
        exists w, T'. split; done.
      * simpl in H1. discriminate.
    + destruct t as [| s t']; simpl in H.
      * discriminate.
      * inversion H. subst.
        have Haux := IH n i t' H2.
        destruct Haux as [w Haux2].
        destruct Haux2 as [T'' Haux3].
        destruct Haux3 as [HT'' Hproj].
        subst T'. exists w, (a :: T'' ). split.
        -- simpl. done.
        -- simpl. rewrite Hproj. done.
Qed.

Lemma projOl_insert : forall (V I O : Ty) n (x : [Times V I] + [Times V O]) (T : seq ([Times V I] + [Times V O])),
    projOl (insert n x T) = insert n (projO x) (projOl T).
Proof.
  intros. elim: n T => [| n IH] T; destruct T; simpl; eauto.
  by rewrite IH.
Qed.

Lemma projIl_insert : forall (V I O : Ty) n (x : [Times V I] + [Times V O]) (T : seq ([Times V I] + [Times V O])),
    projIl (insert n x T) = insert n (projI x) (projIl T).
Proof.
  intros. elim: n T => [| n IH] T; destruct T; simpl; eauto.
  by rewrite IH.
Qed.

(* ---- The converse machinery (uses NI_reduceI / NI_reduceO). ----            *)
(* lthread v L : the stored states in L are rel-related to the f/g state-thread *)
(* from v (a "loose" threading, which is all a real observed trace gives).      *)
Fixpoint lthread (V I O : Ty) (VRel : cRel [V]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) (l : level) (v : [V]) (L : seq ([Times V I] + [Times V O])) : Prop :=
  match L with
  | nil => True
  | inl wi :: L' => rel VRel l (fst wi) (f (snd wi) v) /\ lthread VRel f g l (f (snd wi) v) L'
  | inr wo :: L' => rel VRel l (fst wo) (g (snd wo) v) /\ lthread VRel f g l (g (snd wo) v) L'
  end.

Lemma lthread_stable : forall (V I O : Ty) (VRel : cRel [V]) (IRel : cRel [I]) (ORel : cRel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l L v v',
    fv_NI IRel VRel VRel f -> fv_NI ORel VRel VRel g ->
    rel VRel l v v' -> lthread VRel f g l v L -> lthread VRel f g l v' L.
Proof.
  intros V I O VRel IRel ORel f g l L. elim: L => [|a L' IH] v v' Hf Hg Hvv' Hl; first done.
  destruct a as [[w x]|[w x]]; simpl in *; destruct Hl as [Hw Hl]; split.
  - eapply rel_trans. apply Hw. eapply Hf. apply rel_refl. apply Hvv'.
  - eapply IH. apply Hf. apply Hg. 2: apply Hl. eapply Hf. apply rel_refl. apply Hvv'.
  - eapply rel_trans. apply Hw. eapply Hg. apply rel_refl. apply Hvv'.
  - eapply IH. apply Hf. apply Hg. 2: apply Hl. eapply Hg. apply rel_refl. apply Hvv'.
Qed.

(* The converse: a p-trace (projOl L) lifts to an sta-trace (projIl L).  At an  *)
(* input it re-aligns p's state-component via p's clause 1 + NI_reduceI; at an  *)
(* output it observes p's actual output and continues via NI_reduceO.           *)
Lemma sta_conv : forall (I O V : Ty) (VRel : cRel [V]) (IRel : cRel [I]) (ORel : cRel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l L (p : Proc (Times V I) O) v,
    fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f ->
    NI (eqpair_R VRel IRel) ORel p ->
    Trace ORel l (projOl L) p -> lthread VRel f g l v L ->
    Trace (eqpair VRel ORel) l (projIl L) (sta f g v p).
Proof.
  intros I O V VRel IRel ORel f g l L. elim: L => [|a L' IH] p v Hg Hf HNI HT Hl.
  - simpl. con.
  - destruct a as [[w x]|[w x]]; simpl in *; destruct Hl as [Hw Hl].
    + move: (HNI l) => [Hrel _].
      have Hsw : rel (eqpair_R VRel IRel) l (w,x) (f x v, x) by (left; split; [apply Hw | apply rel_refl]).
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

(* Forward decomposition with the lthread invariant. *)
Lemma sta_proj_lthread : forall (I O V : Ty) (p : Proc (Times V I) O) (VRel : cRel [V]) (IRel : cRel [I]) (ORel : cRel [O]) (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) l v ts,
    fv_NI IRel VRel VRel f -> fv_NI ORel VRel VRel g ->
    Trace (eqpair VRel ORel) l ts (sta f g v p) ->
    exists T, ts = projIl T /\ Trace ORel l (projOl T) p /\ lthread VRel f g l v T.
Proof.
  intros I O V p VRel IRel ORel f g l v ts. move: p v. elim: ts.
  - intros p v Hf Hg HT. exists nil. ssa.
  - intros a ts IH p v Hf Hg HT. inv HT.
    + match_dd. move: (IH _ _ Hf Hg H3) => [T] [Hpi] [Hpo] Hlt.
      exists (inl (f i v, i) :: T). split; [|split].
      * simpl. rewrite Hpi. done.
      * simpl. econ. eauto. apply Hpo.
      * simpl. split. apply rel_refl. apply Hlt.
    + match_dd. destruct o as [vobs oobs].
      move: H2 => /= [HV HO].
      move: (IH _ _ Hf Hg H4) => [T] [Hpi] [Hpo] Hlt.
      exists (inr (vobs, oobs) :: T). split; [|split].
      * simpl. rewrite Hpi. done.
      * simpl. econ. eauto. apply HO. apply Hpo.
      * simpl. split.
        eapply rel_trans. apply rel_sym. apply HV. eapply Hg. apply HO. apply rel_refl.
        eapply lthread_stable. apply Hf. apply Hg. 2: apply Hlt. eapply Hg. apply HO. apply rel_refl.
Qed.

(* Swapping the i-component of one input preserves lthread. *)
Lemma lthread_swap : forall (V I O : Ty) (VRel : cRel [V]) (IRel : cRel [I]) (ORel : cRel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l T'' n w i i' v,
    fv_NI IRel VRel VRel f -> fv_NI ORel VRel VRel g -> rel IRel l i i' ->
    lthread VRel f g l v (insert n (inl (w, i)) T'') ->
    lthread VRel f g l v (insert n (inl (w, i')) T'').
Proof.
  intros V I O VRel IRel ORel f g l T''. elim: T'' => [|a T0 IH] n w i i' v Hf Hg Hii Hl.
  - destruct n; simpl in *.
    + destruct Hl as [Hw _]. split. eapply rel_trans. apply Hw. eapply Hf. apply Hii. apply rel_refl. done.
    + done.
  - destruct n.
    + destruct Hl as [Hw Hl]. split.
      * eapply rel_trans. apply Hw. eapply Hf. apply Hii. apply rel_refl.
      * eapply lthread_stable. apply Hf. apply Hg. 2: apply Hl. eapply Hf. apply Hii. apply rel_refl.
    + simpl in Hl |- *. destruct a as [[w2 x2]|[w2 x2]]; destruct Hl as [Hw2 Hl]; split.
      * apply Hw2.
      * eapply IH. apply Hf. apply Hg. apply Hii. apply Hl.
      * apply Hw2.
      * eapply IH. apply Hf. apply Hg. apply Hii. apply Hl.
Qed.

Lemma lthread_insert_dis : forall (V I O : Ty) (VRel : cRel [V]) (IRel : cRel [I]) (ORel : cRel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l T n i v,
    fv_NI IRel VRel VRel f -> fv_NI ORel VRel VRel g -> f_EP IRel VRel f -> dis IRel l i ->
    lthread VRel f g l v T ->
    exists w, lthread VRel f g l v (insert n (inl (w, i)) T).
Proof.
  intros V I O VRel IRel ORel f g l T n i v Hf Hg Hep Hdi. move: T v. elim: n => [| n' IH] T v Hlt.
  - exists (f i v). simpl. split.
    + apply rel_refl.
    + eapply lthread_stable. apply Hf. apply Hg. 2: apply Hlt.
      apply rel_sym. apply Hep. apply Hdi.
  - destruct T as [| a' T0].
    + exists v. simpl. done.
    + destruct a' as [[w0 i0] | [w0 o0]]; simpl in *; destruct Hlt as [Hw0 Hlt].
      * destruct (IH T0 (f i0 v) Hlt) as [w Hw].
        exists w. split; assumption.
      * destruct (IH T0 (g o0 v) Hlt) as [w Hw].
        exists w. split; assumption.
Qed.

Lemma lthread_remove_dis : forall (V I O : Ty) (VRel : cRel [V]) (IRel : cRel [I]) (ORel : cRel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l T'' n w i v,
    fv_NI IRel VRel VRel f -> fv_NI ORel VRel VRel g -> f_EP IRel VRel f -> dis IRel l i ->
    lthread VRel f g l v (insert n (inl (w, i)) T'') ->
    lthread VRel f g l v T''.
Proof.
  intros V I O VRel IRel ORel f g l T'' n w i v Hf Hg Hep Hdi Hlt.
  move: T'' v Hlt. elim: n => [| n' IH] T'' v Hlt.
  - destruct T'' as [| a' T0]; simpl in Hlt.
    + done.
    + destruct Hlt as [Hw Hlt]. eapply lthread_stable. apply Hf. apply Hg. 2: apply Hlt.
      eapply Hep. apply Hdi.
  - destruct T'' as [| a' T0].
    + simpl. done.
    + destruct a' as [[w0 i0] | [w0 o0]]; simpl in Hlt |- *; destruct Hlt as [Hw0 Hlt].
      * split; [apply Hw0 | eapply IH; eauto].
      * split; [apply Hw0 | eapply IH; eauto].
Qed.

(* sta_NI: clause 1 (rel) is PROVED via the projection + converse approach.     *)
(* Clauses 2 (insert disclosed) and 3 (remove) are analogous (using p's clauses *)
(* 2/3 and f_EP) and are left admitted.                                         *)
Lemma sta_NI : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : cRel [I]) (VRel : cRel [V]) (ORel : cRel [O]),
    fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f -> f_EP IRel VRel f ->
    NI (eqpair_R VRel IRel) ORel p ->
    NI IRel (eqpair VRel ORel) (sta f g v p).
Proof.
  intros I O V p f g v IRel VRel ORel Hg Hf Hep Hp. rewrite /NI /NI_l. intros l. ssa.
  - (* clause 1 (rel) -- PROVED *)
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
    { eapply sta_conv. apply Hg. apply Hf. apply Hp. rewrite projOl_insert. simpl. apply Htp. apply Hl'. }
    rewrite projIl_insert in Hfin. simpl in Hfin. apply Hfin.
  - (* clause 2 (insert disclosed) -- PROVED *)
    intros t i n Hdi HT.
    eapply sta_proj_lthread in HT. 2: apply Hf. 2: apply Hg.
    move: HT => [T] [Heq [Htp Hlt]]. subst t.
    have [w Hw] : exists w, lthread VRel f g l v (insert n (inl (w, i)) T).
    { eapply lthread_insert_dis; eauto. }
    have -> : insert n (inl i) (projIl T) = projIl (insert n (inl (w, i)) T) by rewrite projIl_insert.
    eapply sta_conv. apply Hg. apply Hf. apply Hp. 2: exact Hw.
    rewrite projOl_insert. simpl.
    move: (Hp l) => [_ [Hins _]]. eapply Hins. 2: apply Htp.
    simpl. apply Hdi.
  - (* clause 3 (remove) -- PROVED *)
    intros t i n Hdi HT.
    eapply sta_proj_lthread in HT. 2: apply Hf. 2: apply Hg.
    move: HT => [T] [Heq [Htp Hlt]].
    symmetry in Heq. move/(projIl_insert_inv v) : Heq => [w] [T''] [HT' Ht''].
    subst T. subst t.
    have Hl' : lthread VRel f g l v T''.
    { eapply lthread_remove_dis; eauto. }
    eapply sta_conv. apply Hg. apply Hf. apply Hp. 2: exact Hl'.
    rewrite projOl_insert in Htp. simpl in Htp.
    move: (Hp l) => [_ [_ Hrem]]. eapply Hrem; [|apply Htp].
    simpl. apply Hdi.
Qed.

Inductive SwiTrace (I O : Ty) (ORel : cRel [O]) (BRel : cRel [Bool]) (l : level) : bool -> seq ([Times Bool I] + [Option O]) -> seq ([I] + [Times Bool O]) -> Prop :=
| ST0 b : SwiTrace ORel BRel l b nil nil
| ST1 b b' i t_swi t_p : SwiTrace ORel BRel l (xor b b') t_swi t_p -> SwiTrace ORel BRel l b (inl (b', i) :: t_swi) (inl i :: t_p)
| ST2_false o t_swi t_p : rel (eqmaybe_swi ORel BRel) l None o -> SwiTrace ORel BRel l false t_swi t_p -> SwiTrace ORel BRel l false (inr o :: t_swi) t_p
| ST2_true b_out o o_obs t_swi t_p : rel (eqmaybe_swi ORel BRel) l (Some o) o_obs -> SwiTrace ORel BRel l (negb b_out) t_swi t_p -> SwiTrace ORel BRel l true (inr o_obs :: t_swi) (inr (b_out, o) :: t_p).

Lemma swi_trace : forall (I O : Ty) (p : Proc I (Times Bool O)) (ORel : cRel [O]) (BRel : cRel [Bool]) l b t,
    Trace (eqmaybe_swi ORel BRel) l t (swi b p) ->
    exists t', Trace (eqpair_LR BRel ORel) l t' p /\ SwiTrace ORel BRel l b t t'.
Proof.
  intros I O p ORel BRel l b t HT.
  move: p b HT.
  elim: t => [| a t IH] p b HT.
  - exists nil. split.
    + con.
    + con.
  - inv HT.
    + destruct i as [b' i_in]. dependent destruction H1.
      edestruct (IH p'0 (xor b b') H3) as [t' [Htrace Hswi]].
      exists (inl i_in :: t'). split.
      * econstructor; eauto.
      * econstructor; eauto.
    + dependent destruction H1.
      * edestruct (IH p false H4) as [t' [Htrace Hswi]].
        exists t'. split.
        { exact Htrace. }
        { eapply ST2_false; eauto. }
      * edestruct (IH p'0 (negb b0) H4) as [t' [Htrace Hswi]].
        exists (inr (b0, o0) :: t'). split.
        { econstructor. exact H1. apply rel_refl. exact Htrace. }
        { eapply ST2_true; eauto. }
Qed.

Lemma swi_trace_insert : forall (I O : Ty) (ORel : cRel [O]) (BRel : cRel [Bool]) l b t t' n (i : bool * [I]),
    i.1 = false ->
    SwiTrace ORel BRel l b (insert n (inl i) t) t' ->
    exists n' t'', t' = insert n' (inl i.2) t'' /\ SwiTrace ORel BRel l b t t''.
Proof.
  intros I O ORel BRel l b t t' n i Hi1 H.
  elim: t b t' n H => [| a t IH] b t' n H.
  - ssa. destruct n; simpl in H.
    + inv H. match goal with | Hswi : SwiTrace _ _ _ _ _ _ |- _ => inversion Hswi; subst end.
      exists 0, nil. split; [done | constructor].
    + inv H. exists 1, nil. split; [done | constructor].
  - ssa. destruct n; simpl in H.
    + inv H. exists 0, t_p. split; [done |].
      simpl in Hi1. rewrite Hi1 xorFalse in H4. exact H4.
    + inv H.
      * ssa. match goal with | Hswi : SwiTrace _ _ _ _ _ _ |- _ => destruct (IH _ _ _ Hswi) as [n' [t'' [-> Hswi2]]] end.
        exists n'.+1, (inl i0 :: t''). split; [done |].
        constructor. exact Hswi2.
      * ssa. match goal with | Hswi : SwiTrace _ _ _ _ _ _ |- _ => destruct (IH _ _ _ Hswi) as [n' [t'' [-> Hswi2]]] end.
        exists n', t''. split; [done |].
        eapply ST2_false; eauto.
      * ssa. match goal with | Hswi : SwiTrace _ _ _ _ _ _ |- _ => destruct (IH _ _ _ Hswi) as [n' [t'' [-> Hswi2]]] end.
        exists n'.+1, (inr (b_out, o) :: t''). split; [done |].
        eapply ST2_true; eauto.
Qed.

Lemma swi_trace_insert_conv : forall (I O : Ty) (ORel : cRel [O]) (BRel : cRel [Bool]) l b t t_p n (i : bool * [I]),
    aware BRel true l ->
    dis BRel l i.1 ->
    SwiTrace ORel BRel l b t t_p ->
    exists n', SwiTrace ORel BRel l b (insert n (inl i) t) (insert n' (inl i.2) t_p).
Proof.
  intros I O ORel BRel l b t t_p n [b_in i_in] Haware Hdis Hswi.
  have Hb_in : b_in = false.
  { destruct b_in; [| done].
    have Hrefl : rel BRel l true true by apply: rel_refl.
    have [_ Hnd] := Haware true Hrefl.
    contradiction. }
  rewrite Hb_in.
  elim: t b t_p n Hswi => [| a t IH] b t_p n Hswi.
  - inv Hswi. destruct n; simpl.
    + exists 0. repeat constructor.
    + exists 1. constructor.
  - inv Hswi.
    + destruct n; simpl.
      * exists 0. apply ST1. apply ST1. rewrite xorFalse.
        match goal with | H : SwiTrace _ _ _ _ t _ |- _ => exact H end.
      * ssa. match goal with | H : SwiTrace _ _ _ _ t _ |- _ => destruct (IH _ _ n H) as [n' Hswi_ih] end.
        exists n'.+1. constructor. exact Hswi_ih.
    + destruct n; simpl.
      * exists 0. repeat constructor; eauto.
      * ssa. match goal with | H : SwiTrace _ _ _ _ t _ |- _ => destruct (IH _ _ n H) as [n' Hswi_ih] end.
        exists n'. eapply ST2_false; eauto.
    + destruct n; simpl.
      * exists 0. repeat constructor; eauto.
      * ssa. match goal with | H : SwiTrace _ _ _ _ t _ |- _ => destruct (IH _ _ n H) as [n' Hswi_ih] end.
        exists n'.+1. eapply ST2_true; eauto.
Qed.

Lemma swi_trace_swap : forall (I O : Ty) (ORel : cRel [O]) (BRel : cRel [Bool]) l b t t_p n (i i' : bool * [I]),
    i.1 = i'.1 ->
    SwiTrace ORel BRel l b (insert n (inl i) t) t_p ->
    exists n' t_p', t_p = insert n' (inl i.2) t_p' /\ SwiTrace ORel BRel l b (insert n (inl i') t) (insert n' (inl i'.2) t_p').
Proof.
  intros I O ORel BRel l b t t_p n [b_in i_in] [b_in' i_in'] Heq Hswi.
  simpl in Heq.
  elim: t b t_p n Hswi => [| a t IH] b t_p n Hswi.
  - ssa. destruct n; simpl in Hswi.
    + inv Hswi. match goal with | Hswi' : SwiTrace _ _ _ _ _ _ |- _ => inversion Hswi'; subst end.
      exists 0, nil. split; [done |].
      try rewrite Heq. repeat constructor.
    + inv Hswi. exists 1, nil. split; [done | constructor].
  - ssa. destruct n; simpl in Hswi.
    + inv Hswi. exists 0, t_p0. split; [done |].
      try rewrite Heq. repeat constructor. exact H4.
    + inv Hswi.
      * ssa. match goal with | Hswi' : SwiTrace _ _ _ _ _ _ |- _ => destruct (IH _ _ _ Hswi') as [n' [t_p' [-> Hswi2]]] end.
        exists n'.+1, (inl i :: t_p'). split; [done |].
        constructor. exact Hswi2.
      * ssa. match goal with | Hswi' : SwiTrace _ _ _ _ _ _ |- _ => destruct (IH _ _ _ Hswi') as [n' [t_p' [-> Hswi2]]] end.
        exists n', t_p'. split; [done |].
        eapply ST2_false; eauto.
      * ssa. match goal with | Hswi' : SwiTrace _ _ _ _ _ _ |- _ => destruct (IH _ _ _ Hswi') as [n' [t_p' [-> Hswi2]]] end.
        exists n'.+1, (inr (b_out, o) :: t_p'). split; [done |].
        eapply ST2_true; eauto.
Qed.

Lemma swi_trace_remove : forall (I O : Ty) (ORel : cRel [O]) (BRel : cRel [Bool]) l b t t_p n (i : bool * [I]),
    aware BRel true l ->
    dis BRel l i.1 ->
    SwiTrace ORel BRel l b (insert n (inl i) t) t_p ->
    exists n' t_p', t_p = insert n' (inl i.2) t_p' /\ SwiTrace ORel BRel l b t t_p'.
Proof.
  intros I O ORel BRel l b t t_p n [b_in i_in] Haware Hdis Hswi.
  have Hb_in : b_in = false.
  { destruct b_in; [| done].
    have Hrefl : rel BRel l true true by apply: rel_refl.
    have [_ Hnd] := Haware true Hrefl.
    contradiction. }
  rewrite Hb_in in Hswi.
  elim: t b t_p n Hswi => [| a t IH] b t_p n Hswi.
  - ssa. destruct n; simpl in Hswi.
    + inv Hswi. match goal with | Hswi' : SwiTrace _ _ _ _ _ _ |- _ => inversion Hswi'; subst end.
      exists 0, nil. split; [done | constructor].
    + inv Hswi. exists 1, nil. split; [done | constructor].
  - ssa. destruct n; simpl in Hswi.
    + inv Hswi. exists 0, t_p0. split; [done |].
      rewrite xorFalse in H4. exact H4.
    + inv Hswi.
      * ssa. match goal with | Hswi' : SwiTrace _ _ _ _ _ _ |- _ => destruct (IH _ _ _ Hswi') as [n' [t_p' [-> Hswi2]]] end.
        exists n'.+1, (inl i :: t_p'). split; [done |].
        constructor. exact Hswi2.
      * ssa. match goal with | Hswi' : SwiTrace _ _ _ _ _ _ |- _ => destruct (IH _ _ _ Hswi') as [n' [t_p' [-> Hswi2]]] end.
        exists n', t_p'. split; [done |].
        eapply ST2_false; eauto.
      * ssa. match goal with | Hswi' : SwiTrace _ _ _ _ _ _ |- _ => destruct (IH _ _ _ Hswi') as [n' [t_p' [-> Hswi2]]] end.
        exists n'.+1, (inr (b_out, o) :: t_p'). split; [done |].
        eapply ST2_true; eauto.
Qed.

Lemma swi_conv : forall (I O : Ty) (p : Proc I (Times Bool O)) (ORel : cRel [O]) (BRel : cRel [Bool]) l b t t_p,
    aware BRel true l ->
    Trace (eqpair_LR BRel ORel) l t_p p -> SwiTrace ORel BRel l b t t_p -> Trace (eqmaybe_swi ORel BRel) l t (swi b p).
Proof.
  intros I O p ORel BRel l b t t_p Haware HT Hswi.
  move: p HT.
  elim: Hswi.
  - intros b' p HT. simpl. con.
  - intros b' b'' i t_swi t_p' Hswi IH p HT.
    inv HT.
    econstructor; [eapply reduce_swiI; eauto | eapply IH; exact H3].
  - intros o t_swi t_p' Hrel Hswi IH p HT.
    econstructor; [eapply reduce_swiO; eauto | exact Hrel | eapply IH; exact HT].
  - intros b_out o o_obs t_swi t_p' Hrel Hswi IH p HT.
    inv HT.
    destruct o' as [b_out' o''].
    destruct H2 as [Hb Ho].
    simpl in Hb, Ho.
    have Ho' : rel (eqmaybe_swi ORel BRel) l (Some o'') (Some o) by exact Ho.
    econstructor.
    + eapply reduce_swiO2; [reflexivity | exact H1].
    + eapply rel_trans; [exact Ho' | exact Hrel].
    + destruct b_out', b_out.
      * eapply IH; exact H4.
      * move: (Haware false Hb) => [H_eq _]. discriminate H_eq.
      * move: (rel_sym Hb) => Hb_sym. move: (Haware false Hb_sym) => [H_eq _]. discriminate H_eq.
      * eapply IH; exact H4.
Qed.

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

(* With the new inductive [oblivious ORel p l := forall s, Trace ORel l s p ->
   ObliviousTrace ORel l s], these three lemmas replace the old coinductive
   inversion: they feed a one-longer trace to the hypothesis and invert the
   resulting ObliviousTrace. *)
Lemma oblivious_reduceI : forall (I O : Ty) (ORel : cRel [O]) (p p' : Proc I O) l i,
  oblivious ORel p l -> reduceI p i p' -> oblivious ORel p' l.
Proof.
  intros I O ORel p p' l i H_obl H_red s H_tr.
  have H_tr': Trace ORel l (inl i :: s) p by (eapply TR1; eauto).
  apply H_obl in H_tr'. inv H_tr'. auto.
Qed.

Lemma oblivious_reduceO : forall (I O : Ty) (ORel : cRel [O]) (p p' : Proc I O) l o,
  oblivious ORel p l -> reduceO p o p' -> oblivious ORel p' l.
Proof.
  intros I O ORel p p' l o H_obl H_red s H_tr.
  have H_tr': Trace ORel l (inr o :: s) p by (eapply TR2; [eauto | apply rel_eq | eauto]).
  apply H_obl in H_tr'. inv H_tr'. auto.
Qed.

Lemma oblivious_reduceO_dis : forall (I O : Ty) (ORel : cRel [O]) (p p' : Proc I O) l o,
  oblivious ORel p l -> reduceO p o p' -> dis ORel l o.
Proof.
  intros I O ORel p p' l o H_obl H_red.
  have H_tr': Trace ORel l [:: inr o] p by (eapply TR2; [eauto | apply rel_eq | apply TR0]).
  apply H_obl in H_tr'. inv H_tr'. auto.
Qed.

(* Generalized over the switch state so the trace induction hypothesis stays
   available across the [swi] step. *)
Lemma oblivious_swi_aux : forall (I O : Ty) (ORel : cRel [O]) (BRel : cRel [Bool]) l,
  ~ aware BRel true l ->
  forall s q, Trace (eqmaybe_swi ORel BRel) l s q ->
    forall b (p : Proc I (Times Bool O)), q = swi b p ->
      oblivious (eqpair_R BRel ORel) p l ->
      ObliviousTrace (eqmaybe_swi ORel BRel) l s.
Proof.
  intros I O ORel BRel l H_naware s q Htr.
  induction Htr as [q0 | q0 i q' t HredI Htr IH | q0 o' o q' t HredO Hrel Htr IH];
    intros b p Hq H_obl; subst q0.
  - apply OT_nil.
  - dependent destruction HredI.
    apply OT_cons_in.
    eapply IH; [reflexivity | eapply oblivious_reduceI; eauto].
  - dependent destruction HredO.
    + (* reduce_swiO: output None, process unchanged *)
      apply OT_cons_out.
      * have H_dis_None: dis (eqmaybe_swi ORel BRel) l (@None [O]) by (simpl; exact H_naware).
        apply (proj2 (cRel_rule3 H_dis_None o)); exact Hrel.
      * eapply IH; [reflexivity | exact H_obl].
    + (* reduce_swiO2: output Some o0, inner step reduceO p (b0,o0) p'0 *)
      have H_dis_o0: dis ORel l o0 by (eapply dis_eqpair_R; eapply oblivious_reduceO_dis; eauto).
      apply OT_cons_out.
      * have H_dis_Some: dis (eqmaybe_swi ORel BRel) l (Some o0) by (simpl; exact H_dis_o0).
        apply (proj2 (cRel_rule3 H_dis_Some o)); exact Hrel.
      * eapply IH; [reflexivity | eapply oblivious_reduceO; eauto].
Qed.

Lemma oblivious_swi : forall (I O : Ty) (ORel : cRel [O]) (BRel : cRel [Bool]) (p : Proc I (Times Bool O)) l b,
  ~ aware BRel true l ->
  oblivious (eqpair_R BRel ORel) p l ->
  oblivious (eqmaybe_swi ORel BRel) (swi b p) l.
Proof.
  intros I O ORel BRel p l b H_naware H_obl s Htr.
  eapply oblivious_swi_aux; eauto.
Qed.

Fixpoint all_outputs_dis (I O : Ty) (ORel : cRel [O]) (l : level) (t : seq ([I] + [O])) : Prop :=
  match t with
  | nil => True
  | inl _ :: t' => all_outputs_dis I O ORel l t'
  | inr o :: t' => dis ORel l o /\ all_outputs_dis I O ORel l t'
  end.

Lemma ObliviousTrace_all_outputs_dis : forall (I O : Ty) (ORel : cRel [O]) l t,
  ObliviousTrace ORel l t -> all_outputs_dis I O ORel l t.
Proof.
  intros I O ORel l t H. induction H; simpl; try (split; assumption); auto.
Qed.

Lemma oblivious_trace_any : forall (I O : Ty) (ORel : cRel [O]) (l : level) (p : Proc I O) t,
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
      apply IH; [eapply oblivious_reduceI; eauto | exact H_dis].
    + simpl in H_dis. destruct H_dis as [H_dis_o H_dis_t].
      destruct (Proc_has_output I O p) as [o' [p' HredO]].
      have H_dis_o': dis ORel l o' by (eapply oblivious_reduceO_dis; eauto).
      have H_obl': oblivious ORel p' l by (eapply oblivious_reduceO; eauto).
      have H_rel: rel ORel l o' o.
      { destruct ORel as [dis rel equiv r d i0]. simpl in *.
        move: (i0 l o' H_dis_o' o) => [H_impl1 H_impl2].
        apply H_impl1; auto. }
      eapply TR2; [exact HredO | exact H_rel |].
      apply IH; [exact H_obl' | exact H_dis_t].
Qed.

Lemma oblivious_trace_dis : forall (I O : Ty) (ORel : cRel [O]) (l : level) (p : Proc I O) t,
  oblivious ORel p l ->
  Trace ORel l t p ->
  all_outputs_dis I O ORel l t.
Proof.
  intros I O ORel l p t H_obl H_tr.
  apply H_obl in H_tr. eapply ObliviousTrace_all_outputs_dis; eauto.
Qed.

Lemma all_outputs_dis_insert_inl : forall I O (ORel : cRel [O]) l t n i,
  all_outputs_dis I O ORel l (insert n (inl i) t) <-> all_outputs_dis I O ORel l t.
Proof.
  intros I O ORel l t n i.
  elim: t n.
  - intros n. destruct n; simpl; tauto.
  - intros a t0 IH n. destruct n; simpl.
    + tauto.
    + destruct (IH n) as [Hfwd Hbwd].
      destruct a; simpl.
      * split; auto.
      * split; intros [H1 H2]; split; auto.
Qed.

Lemma oblivious_NI_l : forall (I O : Ty) (IRel : cRel [I]) (ORel : cRel [O]) (p : Proc I O) l,
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

Theorem swi_NI : forall (I O : Ty) (IRel : cRel [I]) (ORel : cRel [O]) (BRel : cRel [Bool]) p b,
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

Fixpoint filter_none {I O : Ty} (t : seq ([Option I] + [O])) : seq ([I] + [O]) :=
  match t with
  | [::] => [::]
  | (inl None) :: t' => filter_none t'
  | (inl (Some i)) :: t' => (inl i) :: filter_none t'
  | (inr o) :: t' => (inr o) :: filter_none t'
  end.

Fixpoint count_not_none {I O : Ty} (n : nat) (t : seq ([Option I] + [O])) : nat :=
  match n with
  | 0 => 0
  | n'.+1 =>
      match t with
      | [::] => 0
      | (inl None) :: t' => count_not_none n' t'
      | _ :: t' => (count_not_none n' t').+1
      end
  end.

Lemma filter_none_insert_none : forall (I O : Ty) n (t : seq ([Option I] + [O])),
    filter_none (insert n (inl None) t) = filter_none t.
Proof.
  move=> I O n t. elim: n t => [|n IH] [|x t] //=.
  case: x => [i|o] //=.
  - case: i => [i|] //=; by rewrite IH.
  - by rewrite IH.
Qed.

Lemma filter_none_insert_some : forall (I O : Ty) n (t : seq ([Option I] + [O])) (x : [I]),
    n <= size t ->
    filter_none (insert n (inl (Some x)) t) = insert (count_not_none n t) (inl x) (filter_none t).
Proof.
  move=> I O n t x. elim: n t => [|n IH] [|y t] //= Hsize.
  case: y => [i|o] //=.
  - case: i => [i|] //=; by rewrite IH.
  - by rewrite IH.
Qed.

Lemma insert_out : forall A n (t : seq A) (a : A), (n <= size t) = false -> insert n a t = t.
Proof.
  move=> A n. elim: n => [|n IH] [|x t] a //= H.
  by rewrite (IH t a H).
Qed.

Lemma filter_none_trace : forall (I O : Ty) (p : Proc I O) (ORel : cRel [O]) l t,
    Trace ORel l t (maybe p) -> Trace ORel l (filter_none t) p.
Proof.
  intros. elim: t p H.
  - ssa.
  - ssa. inv H0.
    + match_dd.
      * apply H in H5. ssa.
      * apply H in H5. ssa. econ; eauto.
    + match_dd.
      apply H in H6. ssa. econ; eauto.
Qed.

Lemma filter_none_trace_back : forall (I O : Ty) (p : Proc I O) (ORel : cRel [O]) l t,
    Trace ORel l (filter_none t) p -> Trace ORel l t (maybe p).
Proof.
  intros I O p ORel l t. elim: t p.
  - ssa.
  - move=> a l0 IH p Ht.
    case: a Ht => [i|o] Ht /=.
    + case: i Ht => [i|] Ht /=.
      * move: IH. inv Ht. match_dd. move=> IH. econ.
        { apply: reduce_maybeI2. apply: H1. }
        { apply: IH. apply: H3. }
      * econ.
        { apply: reduce_maybeI. }
        { apply: IH. apply: Ht. }
    + move: IH. inv Ht. match_dd. move=> IH. econ.
      * apply: reduce_maybeO. apply: H1.
      * apply: H2.
      * apply: IH. apply: H4.
Qed.

Theorem maybe_NI : forall (I O :Ty) (IRel : cRel [I]) (ORel : cRel [O]) p, NI IRel ORel p -> NI (eqmaybe_false IRel) ORel (maybe p).
Proof.
  intros. rewrite /NI /NI_l. ssa.
  - move: (H l). ssa. clear H.
    move/filter_none_trace: H2 => H2.
    apply: filter_none_trace_back.
    case Hsize: (n <= size t).
    + case: i H1 H2 => [x|] H1 H2; case: i' H1 => [y|] H1.
      * rewrite !filter_none_insert_some in H2; last done.
        rewrite !filter_none_insert_some; last done.
        rewrite /NI_l in H0. case: H0 => H0 [H0' H0''].
        apply: (H0 _ _ _ _ H1 H2).
      * case: H1 => H1 _.
        rewrite filter_none_insert_some in H2; last done.
        rewrite filter_none_insert_none.
        rewrite /NI_l in H0. case: H0 => _ [_ H0].
        apply: (H0 _ _ _ H1 H2).
      * case: H1 => _ H1.
        rewrite filter_none_insert_none in H2.
        rewrite filter_none_insert_some; last done.
        rewrite /NI_l in H0. case: H0 => _ [H0 _].
        apply: (H0 _ _ _ H1 H2).
      * rewrite !filter_none_insert_none.
        rewrite !filter_none_insert_none in H2.
        apply: H2.
    + rewrite !insert_out in H2; last done.
      rewrite !insert_out; last done.
      apply: H2.
  - move=> t i n Hdis Htr.
    move/filter_none_trace: Htr => Htr.
    apply: filter_none_trace_back.
    case Hsize: (n <= size t).
    + case: i Hdis => [x|] Hdis.
      * rewrite filter_none_insert_some; last done.
        move: (H l). rewrite /NI_l. ssa. clear H.
      * rewrite filter_none_insert_none. apply: Htr.
    + rewrite insert_out; last done. apply: Htr.
  - move=> t i n Hdis Htr.
    move/filter_none_trace: Htr => Htr.
    apply: filter_none_trace_back.
    case Hsize: (n <= size t).
    + case: i Hdis Htr => [x|] Hdis Htr.
      * rewrite filter_none_insert_some in Htr; last done.
        move: (H l). rewrite /NI_l. ssa. clear H.
        apply: (H2 _ _ _ Hdis Htr).
      * move: Htr. rewrite filter_none_insert_none. move=> Htr. apply: Htr.
    + move: Htr. rewrite insert_out; last done. move=> Htr. apply: Htr.
Qed.

Inductive loop_trace (I : Ty) (IRel : cRel [I]) (l : level) : list ([I] + [I]) -> list ([I] + [I]) -> Prop :=
  | lt_nil : loop_trace IRel l nil nil
  | lt_in : forall i t t', loop_trace IRel l t t' -> loop_trace IRel l (inl i :: t) (inl i :: t')
  | lt_out : forall o o' t t', rel IRel l o' o -> loop_trace IRel l t t' -> loop_trace IRel l (inr o :: t) (inr o :: inl o' :: t').

Lemma Trace_loop_to_p : forall I (IRel : cRel [I]) l t q, Trace IRel l t q -> forall p, q = loop p -> exists t', loop_trace IRel l t t' /\ Trace IRel l t' p.
Proof.
  move=> I IRel l t q H. elim: H.
  - move=> p0 p Heq; subst p0. exists nil; split; first by constructor. by constructor.
  - move=> p0 i p' t0 Hred Htr IH p p0_eq; subst p0.
    inversion Hred; subst.
    have Heq_p := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H.
    subst p0.
    have Heq_i := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H2.
    subst i0.
    have H3' := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H3.
    have H3'' := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H3'.
    have Hsym : p' = loop p'0 by symmetry.
    have [t' [Hlt Htr']]:= IH _ Hsym.
    exists (inl i :: t'); split.
    + by constructor.
    + by apply: (TR1 H4 Htr').
  - move=> p0 o' o p' t0 Hred Hrel Htr IH p p0_eq; subst p0.
    inversion Hred; subst.
    have Heq_p := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H.
    subst p0.
    have Heq_o := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H0.
    subst o0.
    have H3' := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H3.
    have H3'' := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H3'.
    have Hsym : p' = loop p'' by symmetry.
    have [t' [Hlt Htr']]:= IH _ Hsym.
    exists (inr o :: inl o' :: t'); split.
    + by constructor.
    + by apply: (TR2 H4 Hrel (TR1 H5 Htr')).
Qed.

Lemma Trace_p_to_loop : forall I (IRel : cRel [I]) l t t', loop_trace IRel l t t' -> forall p, NI IRel IRel p -> Trace IRel l t' p -> Trace IRel l t (loop p).
Proof.
  move=> I IRel l t t' H. elim: H.
  - move=> p Hni Htr. by constructor.
  - move=> i t0 t'0 Hlt IH p Hni Htr.
    inversion Htr; subst.
    have Hni' := NI_reduceI Hni H1.
    apply: (TR1 (reduce_loopI H1) (IH p' Hni' H3)).
  - move=> o o' t0 t'0 Hrel Hlt IH p Hni Htr.
    inversion Htr; subst.
    inversion H4; subst.
    have Hni' := NI_reduceO Hni H1.
    destruct (equiv IRel l) as [Hrefl Hsym Htrans].
    have Hrel' : rel IRel l o' o'0 by apply: (Htrans _ o); [exact Hrel | apply: Hsym].
    move: (Hni' l). rewrite /NI_l. ssa.
    have Htr'' := H t'0 o' o'0 0 Hrel' H4.
    inversion Htr''; subst.
    have Hni'' := NI_reduceI (NI_reduceO Hni H1) H9.
    apply: (TR2 (reduce_loopO H1 H9) H2 (IH p'1 Hni'' H11)).
Qed.

(* Inserting an input in the external loop trace corresponds to inserting the
   same input at some position in the internal trace. *)
Lemma lt_ins_inl : forall I (IRel : cRel [I]) l t s, loop_trace IRel l t s ->
  forall n i, exists m, loop_trace IRel l (insert n (inl i) t) (insert m (inl i) s).
Proof.
  move=> I IRel l t s H. elim: H.
  - move=> n i. case: n => [|n] /=.
    + by exists 0; do 2 constructor.
    + by exists 1; constructor.
  - move=> i0 t0 s0 Hlt IH n i. case: n => [|n] /=.
    + by exists 0; do 2 constructor.
    + have [m Hm] := IH n i. by exists m.+1; constructor.
  - move=> o o' t0 s0 Hrel Hlt IH n i. case: n => [|n] /=.
    + exists 0 => /=. by apply: lt_in; apply: lt_out.
    + have [m Hm] := IH n i. exists m.+2 => /=. by apply: lt_out.
Qed.

(* The inverse decomposition: a loop trace of an inserted external input splits
   into a loop trace of the base, with the input sitting at some internal
   position; and the same skeleton works for any other input value. *)
Lemma lt_ins_inl_inv : forall I (IRel : cRel [I]) l t n i S,
  loop_trace IRel l (insert n (inl i) t) S ->
  exists m s, loop_trace IRel l t s /\ S = insert m (inl i) s /\
    forall i', loop_trace IRel l (insert n (inl i') t) (insert m (inl i') s).
Proof.
  move=> I IRel l. elim => [|x t0 IH] n i S /=.
  - case: n => [|n] /= H.
    + inversion H; subst. inversion H3; subst.
      exists 0, nil. do 2 (split; first by constructor).
      by move=> i'; do 2 constructor.
    + inversion H; subst.
      exists 1, nil. do 2 (split; first by constructor).
      by move=> i'; constructor.
  - case: n => [|n] /= H.
    + inversion H; subst.
      exists 0, t'. split; first by []. split; first by [].
      by move=> i' /=; constructor.
    + case: x H => [a|a] H.
      * inversion H; subst.
        have [m [s [Hlt0 [Heq Hall]]]] := IH _ _ _ H3.
        exists m.+1, (inl a :: s). split; first by constructor.
        split; first by rewrite /= Heq.
        by move=> i' /=; constructor; apply: Hall.
      * inversion H; subst.
        have [m [s [Hlt0 [Heq Hall]]]] := IH _ _ _ H4.
        exists m.+2, (inr a :: inl o' :: s). split; first by apply: lt_out.
        split; first by rewrite /= Heq.
        by move=> i' /=; apply: lt_out => //; apply: Hall.
Qed.

Theorem loop_NI : forall (I : Ty) (IRel : cRel [I]) p, NI IRel IRel p -> NI IRel IRel (loop p).
Proof.
  move=> I IRel p Hni l. rewrite /NI_l. split; [|split].
  - move=> t i i' n Hrel Htr.
    have [S [Hlt HtrS]] := Trace_loop_to_p Htr erefl.
    have [m [s [Hlt0 [Heq Hall]]]] := lt_ins_inl_inv Hlt.
    rewrite Heq in HtrS.
    move: (Hni l). rewrite /NI_l => -[Hsw _].
    have HtrS' := Hsw _ _ _ _ Hrel HtrS.
    apply: (Trace_p_to_loop (Hall i') Hni HtrS').
  - move=> t i n Hdis Htr.
    have [s [Hlt HtrS]] := Trace_loop_to_p Htr erefl.
    have [m Hltm] := lt_ins_inl Hlt n i.
    move: (Hni l). rewrite /NI_l => -[_ [Hins _]].
    have HtrS' := Hins _ i m Hdis HtrS.
    apply: (Trace_p_to_loop Hltm Hni HtrS').
  - move=> t i n Hdis Htr.
    have [S [Hlt HtrS]] := Trace_loop_to_p Htr erefl.
    have [m [s [Hlt0 [Heq Hall]]]] := lt_ins_inl_inv Hlt.
    rewrite Heq in HtrS.
    move: (Hni l). rewrite /NI_l => -[_ [_ Hrem]].
    have HtrS' := Hrem _ _ _ Hdis HtrS.
    apply: (Trace_p_to_loop Hlt0 Hni HtrS').
Qed.


Definition pl1 (I O1 O2 : Ty) (x : [I] + [Times O1 O2]) : [I] + [O1] :=
  match x with | inl i => inl i | inr o => inr o.1 end.
Definition pl2 (I O1 O2 : Ty) (x : [I] + [Times O1 O2]) : [I] + [O2] :=
  match x with | inl i => inl i | inr o => inr o.2 end.

Lemma map_insert : forall (A B : Set) (f : A -> B) n a l,
  [seq f x | x <- insert n a l] = insert n (f a) [seq f x | x <- l].
Proof. move=> A B f; elim=> [|n IH] a [|x l] //=. by rewrite IH. Qed.

Lemma par_to_proj : forall I O1 O2 (ORel1 : cRel [O1]) (ORel2 : cRel [O2]) l t q,
  Trace (eqpair ORel1 ORel2) l t q ->
  forall (p1 : Proc I O1) (p2 : Proc I O2), q = par p1 p2 ->
  Trace ORel1 l [seq pl1 x | x <- t] p1 /\ Trace ORel2 l [seq pl2 x | x <- t] p2.
Proof.
  move=> I O1 O2 ORel1 ORel2 l t q H. elim: H.
  - move=> p0 p1 p2 Heq. by split; constructor.
  - move=> p0 i p' t0 Hred Htr IH p1 p2 Heq; subst p0.
    inversion Hred; subst.
    have E2 := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H2.
    have ? := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ E2; subst p0.
    have E4 := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H4.
    have ? := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ E4; subst p3.
    have ? := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H5; subst i0.
    have E6 := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H6.
    have ? := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ E6; subst p'.
    have [IH1 IH2] := IH _ _ erefl.
    by split => /=; [apply: (TR1 H3 IH1) | apply: (TR1 H7 IH2)].
  - move=> p0 o' o p' t0 Hred Hrel Htr IH p1 p2 Heq; subst p0.
    inversion Hred; subst.
    have E2 := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H2.
    have ? := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ E2; subst p0.
    have E4 := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H4.
    have ? := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ E4; subst p3.
    have ? := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H3; subst o'.
    have E6 := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H6.
    have ? := @Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ E6; subst p'.
    have [IH1 IH2] := IH _ _ erefl.
    case: Hrel => Hr1 Hr2.
    by split => /=; [apply: (TR2 H5 Hr1 IH1) | apply: (TR2 H7 Hr2 IH2)].
Qed.

Lemma proj_to_par : forall I O1 O2 (ORel1 : cRel [O1]) (ORel2 : cRel [O2]) l t (p1 : Proc I O1) (p2 : Proc I O2),
  Trace ORel1 l [seq pl1 x | x <- t] p1 -> Trace ORel2 l [seq pl2 x | x <- t] p2 ->
  Trace (eqpair ORel1 ORel2) l t (par p1 p2).
Proof.
  move=> I O1 O2 ORel1 ORel2 l. elim=> [|x t0 IH] p1 p2 H1 H2 /=.
  - by constructor.
  - case: x H1 H2 => [i|o] /= H1 H2.
    + inversion H1; subst. inversion H2; subst.
      apply: (TR1 (reduce_parI H3 H4) (IH _ _ H5 H7)).
    + inversion H1; subst. inversion H2; subst.
      have Hr : rel (eqpair ORel1 ORel2) l (o',o'0) o by split; [exact H4|exact H7].
      apply: (TR2 (reduce_parO H3 H5) Hr (IH _ _ H6 H9)).
Qed.

Theorem par_NI : forall (I O1 O2 : Ty) (IRel : cRel [I]) (ORel1 : cRel [O1]) (ORel2 : cRel [O2]) p1 p2,
    NI IRel ORel1 p1 -> NI IRel ORel2 p2 -> NI IRel (eqpair ORel1 ORel2) (par p1 p2).
Proof.
  move=> I O1 O2 IRel ORel1 ORel2 p1 p2 Hni1 Hni2 l. rewrite /NI_l. split; [|split].
  - move=> t i i' n Hrel Htr.
    have [Ht1 Ht2] := par_to_proj Htr erefl.
    rewrite map_insert in Ht1. rewrite map_insert in Ht2.
    move: (Hni1 l) (Hni2 l). rewrite /NI_l => -[Hsw1 _] -[Hsw2 _].
    have Ht1' := Hsw1 _ _ _ _ Hrel Ht1.
    have Ht2' := Hsw2 _ _ _ _ Hrel Ht2.
    apply: proj_to_par; by rewrite map_insert.
  - move=> t i n Hdis Htr.
    have [Ht1 Ht2] := par_to_proj Htr erefl.
    move: (Hni1 l) (Hni2 l). rewrite /NI_l => -[_ [Hin1 _]] -[_ [Hin2 _]].
    have Ht1' := Hin1 _ i n Hdis Ht1.
    have Ht2' := Hin2 _ i n Hdis Ht2.
    apply: proj_to_par; by rewrite map_insert.
  - move=> t i n Hdis Htr.
    have [Ht1 Ht2] := par_to_proj Htr erefl.
    rewrite map_insert in Ht1. rewrite map_insert in Ht2.
    move: (Hni1 l) (Hni2 l). rewrite /NI_l => -[_ [_ Hrm1]] -[_ [_ Hrm2]].
    have Ht1' := Hrm1 _ i n Hdis Ht1.
    have Ht2' := Hrm2 _ i n Hdis Ht2.
    by apply: proj_to_par.
Qed.


(*Definition eqpair_dom (V I : Ty) (VRel : cRel [V]) (IRel : cRel [I])
   (P : [Times V I] -> Prop)
   (Hclo : forall l x y, rel VRel l x.1 y.1 -> rel IRel l x.2 y.2 -> P x -> P y)
   : cRel [Times V I].
  refine (@CRel _
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
    + left. split; eapply cRel_rule1; eauto.
    + right. split; split; try assumption; eapply cRel_rule2; eauto.
  - intros l0 l1 Hord a [Hd Hp]. split; [eapply cRel_rule2; eauto | assumption].
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
Lemma lthread_insert_rel : forall (V I O : Ty) (VRel : cRel [V])
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
Lemma sta_conv' : forall (I O V : Ty) (VRel : cRel [V]) (IRel : cRel [I]) (ORel : cRel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V])
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

Lemma sta_NI' : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : cRel [I]) (VRel : cRel [V]) (ORel : cRel [O])
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
Lemma aware_false_closure : forall (I : Ty) (IRel : cRel [I]) (BRel : cRel [Bool]),
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


Lemma swi_trace_insert_conv_false : forall (I O : Ty) (ORel : cRel [O]) (BRel : cRel [Bool]) l b t t_p n (i : bool * [I]),
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
Qed.*)

(*
(* swi in the eqpair_dom shape: the input base is right-keyed BRel/IRel (the shape *)
(* sta/map produce), and the bool constraint lives in the predicate.              *)
Lemma swi_NI' : forall (I O : Ty) (IRel : cRel [I]) (ORel : cRel [O]) (BRel : cRel [Bool])
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
Qed.*)

(*
(* Map-congruence for eqpair_dom (keystone of the threading): a value map h that  *)
(* is NI on the V-component and carries the predicate P into Q lifts to an f_NI    *)
(* (and f_PU) between the two domain-restricted relations, so map_NI can thread    *)
(* eqpair_dom VRel I (Pf f) (from sta) to eqpair_dom BRel I (bool=false) (for swi). *)
Lemma eqpair_dom_f_NI : forall (V B I : Ty) (VRel : cRel [V]) (BRel : cRel [B]) (IRel : cRel [I])
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

Lemma eqpair_dom_f_PU : forall (V B I : Ty) (VRel : cRel [V]) (BRel : cRel [B]) (IRel : cRel [I])
    (P : [Times V I] -> Prop) (Q : [Times B I] -> Prop) (h : [V] -> [B])
    (HclP : forall l x y, rel VRel l x.1 y.1 -> rel IRel l x.2 y.2 -> P x -> P y)
    (HclQ : forall l x y, rel BRel l x.1 y.1 -> rel IRel l x.2 y.2 -> Q x -> Q y),
    (forall x : [Times V I], P x -> Q (h x.1, x.2)) ->
    f_PU (eqpair_dom VRel IRel P HclP) (eqpair_dom BRel IRel Q HclQ)
         (fun x => (h x.1, x.2)).
Proof.
  intros V B I VRel BRel IRel P Q h HclP HclQ HPQ.
  intros l x [Hd Hp]. split; simpl; [exact Hd | apply HPQ; exact Hp].
Qed.*)
