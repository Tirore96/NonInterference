(* ============================================================================ *)
(* Scratch: verified-in-session snippets for the eqpair_dom / sta_NI' work.      *)
(* Each block below was developed and Qed/Defined'd interactively against        *)
(* current.v's environment (imports NonInterference.theorems + defs eqpair_P,    *)
(* Pf). Paste into current.v as needed. See plan.md and contradiction.txt.       *)
(*                                                                                *)
(* NOTE: these use P = Pf (= image(f)) / the literal closure. Per contradiction   *)
(* .txt, the *real* predicate to use going forward is REACHABILITY (closed under  *)
(* f AND g), with a domain-restricted f_EP. eqpair_dom itself is generic in P and *)
(* is reused unchanged; only the P you instantiate and the f_EP premise change.   *)
(* ============================================================================ *)

(* ---------------------------------------------------------------------------- *)
(* 1. eqpair_dom: lawful domain-restricting myrel combinator (generic in P).     *)
(*    Add `Arguments eqpair_dom {V I} VRel IRel P Hclo` right after it.           *)
(* ---------------------------------------------------------------------------- *)
Definition eqpair_dom (V I : Ty) (VRel : myrel [V]) (IRel : myrel [I]) (P : [Times V I] -> Prop)
  (Hclo : forall l x y, rel VRel l (fst x) (fst y) -> rel IRel l (snd x) (snd y) -> P x -> P y)
  : myrel [Times V I].
  refine (@MyRel _
            (fun l x => dis IRel l (snd x) /\ P x)
            (fun l x y => (rel VRel l (fst x) (fst y) /\ rel IRel l (snd x) (snd y))
                          \/ ((dis IRel l (snd x) /\ P x) /\ (dis IRel l (snd y) /\ P y)))
            _ _ _ _).
  - intro l. constructor.
    + intro x. left. split; apply rel_refl.
    + intros x y [[Hv Hi]|[Ha Hb]].
      * left. split; apply rel_sym; assumption.
      * right. split; assumption.
    + intros x y z H1 H2.
      destruct H1 as [[Hv1 Hi1]|[[Hdx HPx] [Hdy HPy]]];
      destruct H2 as [[Hv2 Hi2]|[[Hdy2 HPy2] [Hdz HPz]]].
      * left. split; eapply rel_trans; eauto.
      * right. split.
        -- split.
           eapply dis_rel_dis2; [apply Hdy2|apply Hi1].
           apply (Hclo l y x); [apply rel_sym; apply Hv1|apply rel_sym; apply Hi1|apply HPy2].
        -- split; assumption.
      * right. split.
        -- split; assumption.
        -- split.
           eapply dis_rel_dis; [apply Hdy|apply Hi2].
           apply (Hclo l y z); [apply Hv2|apply Hi2|apply HPy].
      * right. split; split; assumption.
  - intros l0 l1 Hord a0 a1 [[Hv Hi]|[[Hd0 HP0] [Hd1 HP1]]].
    + left. split; eapply myrel_rule1; eauto.
    + right. split; split; try assumption; eapply myrel_rule2; eauto.
  - intros l0 l1 Hord a [Hd HP]. split; [eapply myrel_rule2; eauto | assumption].
  - intros l a0 [Hd0 HP0] a1. split.
    + intros [Hd1 HP1]. right. split; split; assumption.
    + intros [[Hv Hi]|[_ [Hd1 HP1]]].
      * split.
        eapply dis_rel_dis; [apply Hd0|apply Hi].
        apply (Hclo l a0 a1); [apply Hv|apply Hi|apply HP0].
      * split; assumption.
Defined.
(* Arguments eqpair_dom {V I} VRel IRel P Hclo. *)

(* ---------------------------------------------------------------------------- *)
(* 2. aware_false_closure: bool-side Hclo, discharged from `aware true`.          *)
(* ---------------------------------------------------------------------------- *)
Lemma aware_false_closure : forall (I:Ty)(BRel:myrel [Bool])(IRel:myrel [I]),
  (forall l, aware BRel true l) ->
  forall l (x y:[Times Bool I]),
    rel BRel l (fst x) (fst y) -> rel IRel l (snd x) (snd y) -> fst x = false -> fst y = false.
Proof.
  intros I BRel IRel Haware l x y Hb Hi Hfx.
  rewrite Hfx in Hb.
  destruct (fst y).
  - apply rel_sym in Hb. move: (Haware l false Hb) => [Hc _]. exact Hc.
  - reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. swi_NI' statement in eqpair_dom shape (type-checks; proof TODO).            *)
(*    eqpair_dom's V/I/VRel/IRel/P are implicit until the Arguments line is added,*)
(*    hence the by-name application here.                                         *)
(* ---------------------------------------------------------------------------- *)
Lemma swi_NI'_shape : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (BRel : myrel [Bool])
  (p : Proc I (Times Bool O)) (b : bool) (Haware : forall l, aware BRel true l),
  NI IRel (eqpair_R BRel ORel) p ->
  NI (eqpair_dom (V:=Bool)(I:=I)(VRel:=BRel)(IRel:=IRel)(P:=fun bi => fst bi = false)
        (@aware_false_closure I BRel IRel Haware))
     (eqmaybe_swi ORel BRel) (swi b p).
Proof. Abort.

(* ---------------------------------------------------------------------------- *)
(* 4. Sanity lemmas: eqpair_P over eqpair_R collapses to eqpair_R (why the        *)
(*    witness-based narrowing is vacuous). Documentation only.                    *)
(* ---------------------------------------------------------------------------- *)
Lemma dis_eq : forall (V I:Ty)(VRel:myrel [V])(IRel:myrel [I])(f:[I]->[V]->[V]) l (x:[Times V I]),
  dis (eqpair_P (eqpair_R VRel IRel) (Pf f)) l x <-> dis (eqpair_R VRel IRel) l x.
Proof.
  intros V I VRel IRel f l [v i]. split.
  - intros [H _]. apply H.
  - intros Hd. simpl. split.
    + apply Hd.
    + exists (f i v, i). split.
      * right. split; apply Hd.
      * exists v. reflexivity.
Qed.

Lemma rel_eq : forall (V I:Ty)(VRel:myrel [V])(IRel:myrel [I])(f:[I]->[V]->[V]) l (x y:[Times V I]),
  rel (eqpair_P (eqpair_R VRel IRel) (Pf f)) l x y <-> rel (eqpair_R VRel IRel) l x y.
Proof.
  intros V I VRel IRel f l [v i] [v' i']. split.
  - intros [H|[Ha Hb]].
    + apply H.
    + simpl. right. split; [apply Ha | apply Hb].
  - intros H. left. apply H.
Qed.

Lemma NI_ext : forall (I O:Ty)(R1 R2:myrel [I])(ORel:myrel [O])(p:Proc I O),
  (forall l a b, rel R1 l a b <-> rel R2 l a b) ->
  (forall l a, dis R1 l a <-> dis R2 l a) ->
  NI R1 ORel p -> NI R2 ORel p.
Proof.
  intros I O R1 R2 ORel p Hrel Hdis HNI l.
  move: (HNI l) => [H1 [H2 H3]]. split;[|split].
  - intros t i i' n Hr HT. apply Hrel in Hr. eapply H1; eauto.
  - intros t i n Hd HT. apply Hdis in Hd. eapply H2; eauto.
  - intros t i n Hd HT. apply Hdis in Hd. eapply H3; eauto.
Qed.

Lemma premise_collapses : forall (I O V:Ty)(VRel:myrel [V])(IRel:myrel [I])(ORel:myrel [O])(f:[I]->[V]->[V])(p:Proc (Times V I) O),
  NI (eqpair_R VRel IRel) ORel p <-> NI (eqpair_P (eqpair_R VRel IRel) (Pf f)) ORel p.
Proof.
  intros. split; apply NI_ext; intros.
  - symmetry. apply rel_eq.
  - symmetry. apply dis_eq.
  - apply rel_eq.
  - apply dis_eq.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. sta_conv over eqpair_dom (P = Pf f, literal closure). Builds the converse   *)
(*    direction. Verified for P = Pf; for the reachability P, the body is the     *)
(*    same (the input case uses eqpair_dom's LEFT branch, no P needed).           *)
(* ---------------------------------------------------------------------------- *)
Lemma sta_conv_dom : forall (I O V : Ty) (VRel : myrel [V]) (IRel : myrel [I]) (ORel : myrel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l L (p : Proc (Times V I) O) v
  (Hclo : forall l x y, rel VRel l (fst x) (fst y) -> rel IRel l (snd x) (snd y) -> Pf f x -> Pf f y),
    fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f ->
    NI (eqpair_dom (V:=V)(I:=I)(VRel:=VRel)(IRel:=IRel)(P:=Pf f) Hclo) ORel p ->
    Trace ORel l (projOl L) p -> lthread VRel f g l v L ->
    Trace (eqpair VRel ORel) l (projIl L) (sta f g v p).
Proof.
  intros I O V VRel IRel ORel f g l L p v Hclo Hg Hf HNI HT Hl. move: p v HNI HT Hl. elim: L => [|a L' IH] p v HNI HT Hl.
  - simpl. con.
  - destruct a as [[w x]|[w x]]; simpl in *; destruct Hl as [Hw Hl].
    + move: (HNI l) => [Hrel _].
      have Hsw : rel (eqpair_dom (V:=V)(I:=I)(VRel:=VRel)(IRel:=IRel)(P:=Pf f) Hclo) l (w,x) (f x v, x).
      { left. split; [apply Hw | apply rel_refl]. }
      apply (Hrel (projOl L') (w,x) (f x v, x) 0 Hsw) in HT.
      simpl in HT. inv HT.
      econ. econ. reflexivity. apply H1.
      eapply IH. eapply NI_reduceI. apply HNI. apply H1. apply H3. apply Hl.
    + inv HT.
      econ. econ. reflexivity. apply H1.
      split. eapply rel_trans. eapply Hg. apply H2. apply rel_refl. apply rel_sym. apply Hw. apply H2.
      eapply IH. eapply NI_reduceO. apply HNI. apply H1. apply H4.
      eapply lthread_stable. apply Hf. apply Hg. 2: apply Hl. eapply Hg. apply rel_sym. apply H2. apply rel_refl.
Qed.
(* NB: sta_conv_dom above was assembled from the verified sta_conv' (eqpair_P)    *)
(* body by replacing the rel-witness with eqpair_dom's single LEFT branch. The    *)
(* eqpair_P version is fully Qed'd in session; re-check this one when pasting.     *)
