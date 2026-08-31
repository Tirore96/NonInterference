Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import RelationClasses.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
From HB Require Import structures.
From deriving Require Import deriving.
Require Import Stdlib.Program.Equality.
From Paco Require Import paco.

Import Order.TTheory.
Open Scope order_scope.

Require Export NonInterference.theories.definitions.

(* Two presentations this development departs from, and the results that say the
   departures cost nothing: L-equivalences (section 1) and streams (section 2).
   Prose: README, "Departures from the paper". *)

(* ----------------------------------------------------------------------- *)
(** * 1. L-equivalences                                                     *)

(* Rafnsson et al. (Definition 2) adjoin a distinguished value [*] to the value
   set [V], take an equivalence on [V + {*}] at each level, and call a value
   unobservable at [l] when it is [l]-equivalent to [*].  Here [None] is [*]. *)
Record lEquiv (A : Set) :=
  LEquiv {
      lrel : level -> option A -> option A -> Prop;
      lrel_equiv : forall l, Equivalence (lrel l);
      lrel_mono : forall l0 l1, order l0 l1 ->
                                forall x y, lrel l1 x y -> lrel l0 x y
    }.

(* The two notions an L-equivalence gives rise to: indistinguishability of two
   values, and unobservability of one. *)
Definition lobs (A : Set) (R : lEquiv A) (l : level) (a b : A) :=
  lrel R l (Some a) (Some b).
Definition lunobs (A : Set) (R : lEquiv A) (l : level) (a : A) :=
  lrel R l (Some a) None.

(* The [cEquiv] laws, as plain lemmas at any value set. *)
Lemma rel_mono : forall (A : Set) (C : cEquiv A) l0 l1, order l0 l1 ->
                 forall a0 a1, rel C l1 a0 a1 -> rel C l0 a0 a1.
Proof. intros A C. destruct C. simpl. eauto. Qed.

Lemma dis_mono : forall (A : Set) (C : cEquiv A) l0 l1, order l0 l1 ->
                 forall a, dis C l1 a -> dis C l0 a.
Proof. intros A C. destruct C. simpl. eauto. Qed.

Lemma dis_rel : forall (A : Set) (C : cEquiv A) l a0, dis C l a0 ->
                forall a1, dis C l a1 <-> rel C l a0 a1.
Proof. intros A C. destruct C. simpl. eauto. Qed.

Lemma dis_rel_l : forall (A : Set) (C : cEquiv A) l a b,
    dis C l a -> rel C l a b -> dis C l b.
Proof. intros. eapply (proj2 (dis_rel H b)). eauto. Qed.

Lemma dis_rel_r : forall (A : Set) (C : cEquiv A) l a b,
    dis C l a -> rel C l b a -> dis C l b.
Proof. intros. eapply dis_rel_l; eauto. Qed.

(** ** Every L-equivalence is a characterised equivalence *)

Definition cEquiv_of_lEquiv (A : Set) (R : lEquiv A) : cEquiv A.
  refine (@CEquiv _ (lunobs R) (lobs R) _ _ _ _).
  - intros l. destruct (lrel_equiv R l) as [Hr Hs Ht]. constructor.
    + intros x. apply Hr.
    + intros x y. apply Hs.
    + intros x y z. apply Ht.
  - intros. eapply lrel_mono; eauto.
  - intros. eapply lrel_mono; eauto.
  - intros l a0 H a1. destruct (lrel_equiv R l) as [Hr Hs Ht]. split.
    + intros H1. apply (Ht _ None _); eauto.
    + intros H1. apply (Ht _ (Some a0) _); eauto.
Defined.

(** ** Every characterised equivalence is an L-equivalence *)

(* [None] is related to exactly the distinguished values, so it is a member of
   the distinguished class and of no other. *)
Definition lrel_of_cEquiv (A : Set) (C : cEquiv A) (l : level) (x y : option A) :=
  match x, y with
  | Some a, Some b => rel C l a b
  | Some a, None => dis C l a
  | None, Some b => dis C l b
  | None, None => True
  end.

Lemma lrel_of_cEquiv_refl : forall (A : Set) (C : cEquiv A) l x,
    lrel_of_cEquiv C l x x.
Proof. intros A C l [a|]; simpl; auto using rel_eq. Qed.

Lemma lrel_of_cEquiv_sym : forall (A : Set) (C : cEquiv A) l x y,
    lrel_of_cEquiv C l x y -> lrel_of_cEquiv C l y x.
Proof. intros A C l [a|] [b|]; simpl; auto using rel_sym. Qed.

(* The characterisation law is what makes transitivity through [None] hold: two
   distinguished values are related. *)
Lemma lrel_of_cEquiv_trans : forall (A : Set) (C : cEquiv A) l x y z,
    lrel_of_cEquiv C l x y -> lrel_of_cEquiv C l y z -> lrel_of_cEquiv C l x z.
Proof.
  intros A C l [a|] [b|] [c|]; simpl; intros H0 H1; auto.
  - eapply rel_trans; eauto.
  - eapply dis_rel_l; eauto. apply rel_sym. auto.
  - apply rel_sym. apply (proj1 (dis_rel H0 c)). auto.
  - eapply dis_rel_l; eauto.
Qed.

Definition lEquiv_of_cEquiv (A : Set) (C : cEquiv A) : lEquiv A.
  refine (@LEquiv _ (lrel_of_cEquiv C) _ _).
  - intros l. constructor.
    + intros x. apply lrel_of_cEquiv_refl.
    + intros x y. apply lrel_of_cEquiv_sym.
    + intros x y z. apply lrel_of_cEquiv_trans.
  - intros l0 l1 Hl [a|] [b|]; simpl; intros;
      eauto using rel_mono, dis_mono.
Defined.

(** ** The two presentations say the same thing *)

(* Reading an L-equivalence as a characterised equivalence keeps both notions. *)
Lemma cEquiv_of_lEquiv_rel : forall (A : Set) (R : lEquiv A) l a b,
    rel (cEquiv_of_lEquiv R) l a b <-> lobs R l a b.
Proof. reflexivity. Qed.

Lemma cEquiv_of_lEquiv_dis : forall (A : Set) (R : lEquiv A) l a,
    dis (cEquiv_of_lEquiv R) l a <-> lunobs R l a.
Proof. reflexivity. Qed.

(* And so does reading a characterised equivalence as an L-equivalence. *)
Lemma lEquiv_of_cEquiv_obs : forall (A : Set) (C : cEquiv A) l a b,
    lobs (lEquiv_of_cEquiv C) l a b <-> rel C l a b.
Proof. reflexivity. Qed.

Lemma lEquiv_of_cEquiv_unobs : forall (A : Set) (C : cEquiv A) l a,
    lunobs (lEquiv_of_cEquiv C) l a <-> dis C l a.
Proof. reflexivity. Qed.

(* The two translations are inverse to each other. *)
Theorem lEquiv_of_cEquivK : forall (A : Set) (R : lEquiv A) l x y,
    lrel (lEquiv_of_cEquiv (cEquiv_of_lEquiv R)) l x y <-> lrel R l x y.
Proof.
  intros A R l x y. destruct (lrel_equiv R l) as [Hr Hs Ht].
  destruct x as [a|]; destruct y as [b|]; simpl.
  all: try reflexivity.
  all: try (split; apply Hs).
  all: split; auto.
  all: intros _; apply Hr.
Qed.

Theorem cEquiv_of_lEquivK : forall (A : Set) (C : cEquiv A) l,
    (forall a b, rel (cEquiv_of_lEquiv (lEquiv_of_cEquiv C)) l a b <-> rel C l a b) /\
    (forall a, dis (cEquiv_of_lEquiv (lEquiv_of_cEquiv C)) l a <-> dis C l a).
Proof. intros. split; reflexivity. Qed.

(* [Trace] and [NI] read the two fields and nothing else, so equivalences that
   agree on them accept the same processes. *)
Lemma Trace_ext : forall (I O : Ty) (ORel ORel' : cEquiv [O]) l t (p : Proc I O),
    (forall o o', rel ORel l o o' -> rel ORel' l o o') ->
    Trace ORel l t p -> Trace ORel' l t p.
Proof. intros I O ORel ORel' l t p Hr H. induction H; econstructor; eauto. Qed.

Lemma NI_ext : forall (I O : Ty) (IRel IRel' : cEquiv [I]) (ORel ORel' : cEquiv [O]) p,
    (forall l i i', rel IRel l i i' <-> rel IRel' l i i') ->
    (forall l i, dis IRel l i <-> dis IRel' l i) ->
    (forall l o o', rel ORel l o o' <-> rel ORel' l o o') ->
    NI IRel ORel p -> NI IRel' ORel' p.
Proof.
  intros I O IRel IRel' ORel ORel' p Hi Hd Ho H l.
  destruct (H l) as [Hsub [Hins Hdel]].
  split; [|split]; intros.
  - eapply Trace_ext. intros. apply Ho. eauto.
    apply Hsub with (i:=i). apply Hi. eauto.
    eapply Trace_ext. intros. apply Ho. eauto. eauto.
  - eapply Trace_ext. intros. apply Ho. eauto.
    apply Hins. apply Hd. eauto.
    eapply Trace_ext. intros. apply Ho. eauto. eauto.
  - eapply Trace_ext. intros. apply Ho. eauto.
    apply Hdel with (i:=i) (n:=n). apply Hd. eauto.
    eapply Trace_ext. intros. apply Ho. eauto. eauto.
Qed.

(* Both notions survive the round trip unchanged, so non-interference stated over
   L-equivalences and non-interference stated over characterised equivalences hold
   of exactly the same processes. *)
Theorem NI_lEquiv : forall (I O : Ty) (CI : cEquiv [I]) (CO : cEquiv [O]) p,
    NI CI CO p <->
    NI (cEquiv_of_lEquiv (lEquiv_of_cEquiv CI)) (cEquiv_of_lEquiv (lEquiv_of_cEquiv CO)) p.
Proof. intros. split; apply NI_ext; intros; reflexivity. Qed.

(* ----------------------------------------------------------------------- *)
(** * 2. Streams                                                            *)

CoInductive stream (A : Set) : Set := scons : A -> stream A -> stream A.
Arguments scons {A} a s.

Definition shd (A : Set) (s : stream A) := let: scons a _ := s in a.
Definition stl (A : Set) (s : stream A) := let: scons _ s' := s in s'.

Definition sunfold (A : Set) (s : stream A) := let: scons a s' := s in scons a s'.

Lemma sunfoldE : forall (A : Set) (s : stream A), s = sunfold s.
Proof. intros A [a s]. reflexivity. Qed.

Fixpoint sprefix (A : Set) (n : nat) (s : stream A) : seq A :=
  match n with
  | 0 => nil
  | n'.+1 => shd s :: sprefix n' (stl s)
  end.

Fixpoint sapp (A : Set) (t : seq A) (s : stream A) : stream A :=
  match t with
  | nil => s
  | a::t' => scons a (sapp t' s)
  end.

Fixpoint sinsert (A : Set) (n : nat) (a : A) (s : stream A) : stream A :=
  match n with
  | 0 => scons a s
  | n'.+1 => scons (shd s) (sinsert n' a (stl s))
  end.

(* The stream reading of [Trace]: [p] performs the whole stream, with each output
   only required to be indistinguishable from the one recorded. *)
Variant STraceF (I O : Ty) (ORel : cEquiv [O]) (l : level)
        (R : stream ([I] + [O]) -> Proc I O -> Prop) :
  stream ([I] + [O]) -> Proc I O -> Prop :=
| STR1 p i p' s : reduceI p i p' -> R s p' -> STraceF ORel l R (scons (inl i) s) p
| STR2 p o' o p' s : reduceO p o' p' -> rel ORel l o' o -> R s p' ->
                     STraceF ORel l R (scons (inr o) s) p.

Lemma monotone_STraceF : forall (I O : Ty) (ORel : cEquiv [O]) l,
    monotone2 (@STraceF I O ORel l).
Proof. intros I O ORel l x0 x1 r r' IN LE. inv IN; econstructor; eauto. Qed.
Hint Resolve monotone_STraceF : paco.

Definition STrace (I O : Ty) (ORel : cEquiv [O]) (l : level)
  (s : stream ([I] + [O])) (p : Proc I O) := paco2 (@STraceF I O ORel l) bot2 s p.

Definition SNI_l (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (l : level) (p : Proc I O) : Prop :=
  (forall s i i' n, rel IRel l i i' -> STrace ORel l (sinsert n (inl i) s) p -> STrace ORel l (sinsert n (inl i') s) p) /\
  (forall s i n, dis IRel l i -> STrace ORel l s p -> STrace ORel l (sinsert n (inl i) s) p) /\
  (forall s i n, dis IRel l i -> STrace ORel l (sinsert n (inl i) s) p -> STrace ORel l s p).

Definition SNI (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O) :=
  forall l, SNI_l IRel ORel l p.

(** ** Reduction is a total function *)

(* Both reduction relations are deterministic and defined everywhere, so a
   process is a machine that can always take one more step.  This is what lets a
   finite trace be extended to a stream. *)
Fixpoint stepI (I O : Ty) (p : Proc I O) : [I] -> Proc I O :=
  match p in Proc I O return [I] -> Proc I O with
  | @out _ _ o => fun _ => out o
  | @map _ _ _ _ f g q => fun i => map f g (stepI q (f i))
  | @sta _ _ _ f g v q => fun i => sta f g (f i v) (stepI q (f i v, i))
  | @swi _ _ b q => fun i => swi (xor b i.1) (stepI q i.2)
  | @par _ _ _ q1 q2 => fun i => par (stepI q1 i) (stepI q2 i)
  | @loop _ q => fun i => loop (stepI q i)
  | @maybe _ _ q => fun i => match i with
                        | None => maybe q
                        | Some i' => maybe (stepI q i')
                        end
  end.

Fixpoint stepO (I O : Ty) (p : Proc I O) : [O] * Proc I O :=
  match p in Proc I O return [O] * Proc I O with
  | @out _ _ o => (o, out o)
  | @map _ _ _ _ f g q => let: (o,q') := stepO q in (g o, map f g q')
  | @sta _ _ _ f g v q => let: (o,q') := stepO q in ((g o v, o), sta f g (g o v) q')
  | @swi _ _ b q => match b with
               | true => let: (bo,q') := stepO q in (Some bo.2, swi (xor true bo.1) q')
               | false => (None, swi false q)
               end
  | @par _ _ _ q1 q2 => let: (o1,q1') := stepO q1 in let: (o2,q2') := stepO q2 in
                 ((o1,o2), par q1' q2')
  | @loop _ q => let: (o,q') := stepO q in (o, loop (stepI q' o))
  | @maybe _ _ q => let: (o,q') := stepO q in (o, maybe q')
  end.

Lemma reduceI_step : forall (I O : Ty) (p : Proc I O) i, reduceI p i (stepI p i).
Proof.
  intros I O p. induction p; intros; simpl; eauto.
  - destruct i as [b' i]. econstructor; eauto.
  - destruct i as [i'|]; eauto.
Qed.

Lemma reduceI_det : forall (I O : Ty) (p : Proc I O) i p',
    reduceI p i p' -> p' = stepI p i.
Proof.
  intros I O p i p' H. induction H; simpl; subst.
  all: try rewrite IHreduceI.
  all: try rewrite IHreduceI1.
  all: try rewrite IHreduceI2.
  all: reflexivity.
Qed.

Lemma reduceO_step : forall (I O : Ty) (p : Proc I O), reduceO p (stepO p).1 (stepO p).2.
Proof.
  intros I O p. induction p; simpl; eauto.
  - destruct (stepO p); simpl in *; eauto.
  - destruct (stepO p); simpl in *; eauto.
  - destruct b.
    + destruct (stepO p) as [[b' o] q]; simpl in *. econstructor; eauto.
    + econstructor.
  - destruct (stepO p1); destruct (stepO p2); simpl in *; eauto.
  - destruct (stepO p) as [o q]; simpl in *. econstructor; eauto.
    apply reduceI_step.
  - destruct (stepO p); simpl in *; eauto.
Qed.

Lemma reduceO_det : forall (I O : Ty) (p : Proc I O) o p',
    reduceO p o p' -> (o,p') = stepO p.
Proof.
  intros I O p o p' H. induction H; simpl; subst.
  all: try (apply reduceI_det in H0; subst).
  all: try rewrite -IHreduceO.
  all: try rewrite -IHreduceO1.
  all: try rewrite -IHreduceO2.
  all: reflexivity.
Qed.

(** ** Finite traces are the prefixes of stream traces *)

Lemma STrace_sprefix : forall (I O : Ty) (ORel : cEquiv [O]) l s (p : Proc I O),
    STrace ORel l s p -> forall n, Trace ORel l (sprefix n s) p.
Proof.
  intros I O ORel l s p H n. revert s p H.
  induction n; intros s p H; simpl. constructor.
  punfold H.
  destruct H as [q i q' s0 Hred HR | q o' o q' s0 Hred Hrel HR]; simpl.
  - econstructor. eauto. apply IHn. pclearbot. auto.
  - econstructor. eauto. eauto. apply IHn. pclearbot. auto.
Qed.

Lemma sprefix_STrace : forall (I O : Ty) (ORel : cEquiv [O]) l s (p : Proc I O),
    (forall n, Trace ORel l (sprefix n s) p) -> STrace ORel l s p.
Proof.
  intros I O ORel l. pcofix CIH. intros s p H. destruct s as [[i|o] s].
  - pfold. apply STR1 with (p':=stepI p i). apply reduceI_step.
    right. apply CIH. intros n. move: (H n.+1) => Hn. simpl in Hn.
    inversion Hn; subst.
    match goal with Hr : reduceI _ _ _ |- _ => apply reduceI_det in Hr; subst end.
    auto.
  - move: (H 1) => H1. simpl in H1. inversion H1; subst.
    match goal with Hr : reduceO _ _ _ |- _ => move: (reduceO_det Hr) => Ho end.
    pfold. apply STR2 with (o':=(stepO p).1) (p':=(stepO p).2). apply reduceO_step.
    rewrite -Ho. auto.
    right. apply CIH. intros n. move: (H n.+1) => Hn. simpl in Hn.
    inversion Hn; subst.
    match goal with Hr : reduceO _ _ _ |- _ => move: (reduceO_det Hr) => Ho' end.
    rewrite -Ho'. auto.
Qed.

Lemma sprefix_sinsert_le : forall (A : Set) n k (a : A) s,
    k <= n -> sprefix k (sinsert n a s) = sprefix k s.
Proof.
  induction n; intros k a s Hk; destruct k; try reflexivity; try done.
  simpl. rewrite IHn //.
Qed.

Lemma sprefix_sinsert_gt : forall (A : Set) n k (a : A) s,
    n < k -> sprefix k (sinsert n a s) = insert n a (sprefix k.-1 s).
Proof.
  intros A.
  have sprefixS : (forall k (s : stream A), sprefix k.+1 s = shd s :: sprefix k (stl s)) by [].
  induction n; intros k a s Hk; destruct k as [|k]; try done.
  destruct k as [|k]; try done. simpl.
  rewrite -(sprefixS k (sinsert n a (stl s))) IHn //.
Qed.

Lemma sprefix_sapp : forall (A : Set) (t : seq A) s, sprefix (size t) (sapp t s) = t.
Proof. induction t; intros; simpl; auto. rewrite IHt //. Qed.

Lemma sinsert_sapp : forall (A : Set) n (a : A) t s,
    n <= size t -> sinsert n a (sapp t s) = sapp (insert n a t) s.
Proof.
  induction n; intros a t s H; simpl. reflexivity.
  destruct t as [|b t]; try done. simpl. rewrite IHn //.
Qed.

(* Past the end of the list there is nothing to insert into. *)
Lemma insert_oversize : forall (A : Set) n (a : A) t, size t < n -> insert n a t = t.
Proof.
  induction n; intros a t H; try done.
  destruct t as [|b t]. reflexivity. simpl. rewrite IHn //.
Qed.

(** ** Every finite trace extends to a stream trace *)

(* The process keeps running on its own outputs. *)
CoFixpoint follow (I O : Ty) (p : Proc I O) : stream ([I] + [O]) :=
  scons (inr (stepO p).1) (follow (stepO p).2).

Lemma STrace_follow : forall (I O : Ty) (ORel : cEquiv [O]) l (p : Proc I O),
    STrace ORel l (follow p) p.
Proof.
  intros I O ORel l. pcofix CIH. intros p. rewrite (sunfoldE (follow p)). simpl.
  pfold. apply STR2 with (o':=(stepO p).1) (p':=(stepO p).2).
  apply reduceO_step. apply rel_eq. right. apply CIH.
Qed.

Fixpoint runT (I O : Ty) (t : seq ([I] + [O])) (p : Proc I O) : Proc I O :=
  match t with
  | nil => p
  | inl i :: t' => runT t' (stepI p i)
  | inr _ :: t' => runT t' (stepO p).2
  end.

Lemma Trace_STrace : forall (I O : Ty) (ORel : cEquiv [O]) l t (p : Proc I O),
    Trace ORel l t p -> STrace ORel l (sapp t (follow (runT t p))) p.
Proof.
  intros I O ORel l t p H. induction H; simpl.
  - apply STrace_follow.
  - move: (reduceI_det H) => Hd. subst. pfold.
    apply STR1 with (p':=stepI p i). auto. left. auto.
  - move: (reduceO_det H) => Hd. rewrite -Hd. simpl. pfold.
    apply STR2 with (o':=o') (p':=p'); auto.
Qed.

Corollary Trace_stream : forall (I O : Ty) (ORel : cEquiv [O]) l t (p : Proc I O),
    Trace ORel l t p -> exists r, STrace ORel l (sapp t r) p.
Proof. intros. exists (follow (runT t p)). apply Trace_STrace. auto. Qed.

(** ** The list and stream definitions accept the same processes *)

(* A stream trace is what all its prefixes say it is. *)
Lemma SNI_of_NI : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O),
    NI IRel ORel p -> SNI IRel ORel p.
Proof.
  intros I O IRel ORel p H l. destruct (H l) as [Hsub [Hins Hdel]].
  split; [|split].
  (* substitution *)
  intros s i i' n Hr Hs. apply sprefix_STrace. intros k.
  case: (leqP k n) => Hk.
  rewrite sprefix_sinsert_le //. move: (STrace_sprefix Hs k).
  rewrite sprefix_sinsert_le //.
  rewrite sprefix_sinsert_gt //. apply Hsub with (i:=i) => //.
  move: (STrace_sprefix Hs k). rewrite sprefix_sinsert_gt //.
  (* insertion *)
  intros s i n Hd Hs. apply sprefix_STrace. intros k.
  case: (leqP k n) => Hk.
  rewrite sprefix_sinsert_le //. apply (STrace_sprefix Hs).
  rewrite sprefix_sinsert_gt //. apply Hins => //. apply (STrace_sprefix Hs).
  (* deletion: one more label of the stream than the prefix asked for *)
  intros s i n Hd Hs. apply sprefix_STrace. intros k.
  case: (leqP k n) => Hk.
  move: (STrace_sprefix Hs k). rewrite sprefix_sinsert_le //.
  move: (STrace_sprefix Hs k.+1). rewrite sprefix_sinsert_gt //=.
  apply Hdel with (i:=i) (n:=n) => //.
  by apply: (leq_trans Hk (leqnSn k)).
Qed.

(* A finite trace is a prefix of a stream trace, because the process can always
   take one more step. *)
Lemma NI_of_SNI : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O),
    SNI IRel ORel p -> NI IRel ORel p.
Proof.
  intros I O IRel ORel p H l. destruct (H l) as [Hsub [Hins Hdel]].
  split; [|split].
  - intros t i i' n Hr Ht. case: (leqP n (size t)) => Hn.
    + move: (Trace_stream Ht) => [r Hr']. rewrite -sinsert_sapp // in Hr'.
      move: (Hsub _ _ i' _ Hr Hr') => Hr''. rewrite sinsert_sapp // in Hr''.
      move: (STrace_sprefix Hr'' (size (insert n (inl i') t))).
      rewrite sprefix_sapp //.
    + rewrite insert_oversize //. rewrite insert_oversize // in Ht.
  - intros t i n Hd Ht. case: (leqP n (size t)) => Hn.
    + move: (Trace_stream Ht) => [r Hr']. move: (Hins _ i n Hd Hr') => Hr''.
      rewrite sinsert_sapp // in Hr''.
      move: (STrace_sprefix Hr'' (size (insert n (inl i) t))).
      rewrite sprefix_sapp //.
    + rewrite insert_oversize //.
  - intros t i n Hd Ht. case: (leqP n (size t)) => Hn.
    + move: (Trace_stream Ht) => [r Hr']. rewrite -sinsert_sapp // in Hr'.
      move: (Hdel _ i n Hd Hr') => Hr''.
      move: (STrace_sprefix Hr'' (size t)). rewrite sprefix_sapp //.
    + rewrite insert_oversize // in Ht.
Qed.

(* Reading traces as finite lists and reading them as streams give the same
   non-interference property. *)
Theorem NI_SNI : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O),
    NI IRel ORel p <-> SNI IRel ORel p.
Proof. intros. split. apply SNI_of_NI. apply NI_of_SNI. Qed.

(* ----------------------------------------------------------------------- *)
(** * 3. Obliviousness                                                      *)

(* The paper (Definition 10) states obliviousness coinductively over reductions:
   every output a process can reach is unobservable.  Here it is stated over the
   traces a process admits, and it asks for one indistinguishability class rather
   than for the distinguished one.  The two departures are separated below.
   [ObliviousAt] is the paper's shape at this development's condition, and
   [ObliviousDis] is the paper's condition. *)

Variant ObliviousAtF (I O : Ty) (ORel : cEquiv [O]) (l : level) (o0 : [O])
        (R : Proc I O -> Prop) : Proc I O -> Prop :=
| OAF p : (forall i p', reduceI p i p' -> R p') ->
          (forall o p', reduceO p o p' -> rel ORel l o0 o /\ R p') ->
          ObliviousAtF ORel l o0 R p.

Lemma monotone_ObliviousAtF : forall (I O : Ty) (ORel : cEquiv [O]) l o0,
    monotone1 (@ObliviousAtF I O ORel l o0).
Proof.
  intros I O ORel l o0 x0 r r' IN LE. inv IN. constructor.
  - intros. apply LE. eauto.
  - intros. move: (H0 _ _ H1) => [Hr Hp]. split; auto.
Qed.
Hint Resolve monotone_ObliviousAtF : paco.

Definition ObliviousAt (I O : Ty) (ORel : cEquiv [O]) (l : level) (o0 : [O])
  (p : Proc I O) := paco1 (@ObliviousAtF I O ORel l o0) bot1 p.

(* Shape: quantifying over reachable states and quantifying over admitted traces
   come to the same thing.  Neither direction needs reduction to be a function. *)
Lemma ObliviousAt_oblivious_at : forall (I O : Ty) (ORel : cEquiv [O]) l o0 (p : Proc I O),
    ObliviousAt ORel l o0 p -> oblivious_at ORel o0 p l.
Proof.
  intros I O ORel l o0 p H s Hs. revert H.
  induction Hs as [q | q i q' t Hred Hs IH | q o' o q' t Hred Hrel Hs IH];
    intros HO.
  - constructor.
  - punfold HO. destruct HO as [r Hi Ho]. constructor. apply IH.
    move: (Hi _ _ Hred). intros [X|X]; [auto | destruct X].
  - punfold HO. destruct HO as [r Hi Ho]. move: (Ho _ _ Hred) => [Hr HO'].
    constructor. eapply rel_trans; eauto. apply IH.
    destruct HO' as [X|X]; [auto | destruct X].
Qed.

Lemma oblivious_at_ObliviousAt : forall (I O : Ty) (ORel : cEquiv [O]) l o0 (p : Proc I O),
    oblivious_at ORel o0 p l -> ObliviousAt ORel l o0 p.
Proof.
  intros I O ORel l o0. pcofix CIH. intros p H. pfold. constructor.
  - intros i p' Hred. right. apply CIH. intros s Hs.
    move: (H (inl i :: s) (TR1 Hred Hs)) => Ho. inversion Ho; subst. auto.
  - intros o p' Hred. split.
    + move: (H [:: inr o] (TR2 Hred (rel_eq ORel o l) (TR0 ORel l p'))) => Ho.
      inversion Ho; subst. auto.
    + right. apply CIH. intros s Hs.
      move: (H (inr o :: s) (TR2 Hred (rel_eq ORel o l) Hs)) => Ho.
      inversion Ho; subst. auto.
Qed.

Theorem ObliviousAt_iff : forall (I O : Ty) (ORel : cEquiv [O]) l o0 (p : Proc I O),
    ObliviousAt ORel l o0 p <-> oblivious_at ORel o0 p l.
Proof.
  intros. split. apply ObliviousAt_oblivious_at. apply oblivious_at_ObliviousAt.
Qed.

(* The paper's condition: every reachable output is unobservable. *)
Variant ObliviousDisF (I O : Ty) (ORel : cEquiv [O]) (l : level)
        (R : Proc I O -> Prop) : Proc I O -> Prop :=
| ODF p : (forall i p', reduceI p i p' -> R p') ->
          (forall o p', reduceO p o p' -> dis ORel l o /\ R p') ->
          ObliviousDisF ORel l R p.

Lemma monotone_ObliviousDisF : forall (I O : Ty) (ORel : cEquiv [O]) l,
    monotone1 (@ObliviousDisF I O ORel l).
Proof.
  intros I O ORel l x0 r r' IN LE. inv IN. constructor.
  - intros. apply LE. eauto.
  - intros. move: (H0 _ _ H1) => [Hr Hp]. split; auto.
Qed.
Hint Resolve monotone_ObliviousDisF : paco.

Definition ObliviousDis (I O : Ty) (ORel : cEquiv [O]) (l : level) (p : Proc I O) :=
  paco1 (@ObliviousDisF I O ORel l) bot1 p.

(* Unobservable outputs are all in one class, so the paper's condition is one way
   of meeting this development's. *)
Lemma ObliviousDis_ObliviousAt : forall (I O : Ty) (ORel : cEquiv [O]) l (p : Proc I O) o0,
    dis ORel l o0 -> ObliviousDis ORel l p -> ObliviousAt ORel l o0 p.
Proof.
  intros I O ORel l p o0 Hd. move: p. pcofix CIH. intros p H.
  punfold H. destruct H as [q Hi Ho]. pfold. constructor.
  - intros i p' Hred. right. apply CIH.
    move: (Hi _ _ Hred). intros [X|X]; [auto | destruct X].
  - intros o p' Hred. move: (Ho _ _ Hred) => [Hdo HD]. split.
    + apply dis_dis_rel; assumption.
    + right. apply CIH. destruct HD as [X|X]; [auto | destruct X].
Qed.

(* Every process emits, so a reference output is always available. *)
Theorem oblivious_of_ObliviousDis : forall (I O : Ty) (ORel : cEquiv [O]) l (p : Proc I O),
    ObliviousDis ORel l p -> oblivious ORel p l.
Proof.
  intros I O ORel l p H.
  have Hd : dis ORel l (stepO p).1.
  { punfold H. destruct H as [q Hi Ho]. move: (Ho _ _ (reduceO_step q)) => [] //. }
  exists (stepO p).1. apply ObliviousAt_oblivious_at.
  apply (@ObliviousDis_ObliviousAt I O ORel l p ((stepO p).1) Hd H).
Qed.

(* The converse fails, so the weakening is strict.  A constant process under
   [public_equiv] stays in one class, the singleton holding its own output, and
   [public_equiv] leaves the distinguished class empty. *)
Lemma ObliviousAt_out : forall (I O : Ty) (ORel : cEquiv [O]) l (o : [O]),
    ObliviousAt ORel l o (@out I O o).
Proof.
  intros I O ORel l o. pcofix CIH. pfold. constructor.
  - intros i p' Hred. move: (reduceI_det Hred) => /= ->. right. apply CIH.
  - intros o1 p' Hred. move: (reduceO_det Hred) => /= [] -> ->.
    split. apply rel_eq. right. apply CIH.
Qed.

Lemma oblivious_out_public : forall (I O : Ty) (o : [O]) l,
    oblivious (public_equiv O) (@out I O o) l.
Proof.
  intros I O o l. exists o. apply ObliviousAt_oblivious_at. apply ObliviousAt_out.
Qed.

(* Under [public_equiv] the distinguished class is empty and every process emits,
   so nothing at all meets the paper's condition. *)
Lemma not_ObliviousDis_public : forall (I O : Ty) (p : Proc I O) l,
    ~ ObliviousDis (public_equiv O) l p.
Proof.
  intros I O p l H. punfold H. destruct H as [q Hi Ho].
  move: (Ho _ _ (reduceO_step q)) => [] //.
Qed.

(* ----------------------------------------------------------------------- *)
(** * 4. The paper's non-interference                                       *)

(* Definition 4 quantifies over the streams a process performs, which is
   [STraceF] without the [rel] on outputs. *)
Variant PerformsF (I O : Ty) (R : stream ([I] + [O]) -> Proc I O -> Prop) :
  stream ([I] + [O]) -> Proc I O -> Prop :=
| PF1 p i p' s : reduceI p i p' -> R s p' -> PerformsF R (scons (inl i) s) p
| PF2 p o p' s : reduceO p o p' -> R s p' -> PerformsF R (scons (inr o) s) p.

Lemma monotone_PerformsF : forall (I O : Ty), monotone2 (@PerformsF I O).
Proof. intros I O x0 x1 r r' IN LE. inv IN; econstructor; eauto. Qed.
Hint Resolve monotone_PerformsF : paco.

Definition Performs (I O : Ty) (s : stream ([I] + [O])) (p : Proc I O) :=
  paco2 (@PerformsF I O) bot2 s p.

(* Definition 3, clause for clause. *)
Definition Clause1 (I O : Ty) (IRel : cEquiv [I]) (l : level)
  (R : stream ([I] + [O]) -> Proc I O -> Prop) s (p : Proc I O) : Prop :=
  forall i s', s = scons (inl i) s' -> dis IRel l i -> R s' p.

Definition Clause2 (I O : Ty) (IRel : cEquiv [I]) (l : level)
  (R : stream ([I] + [O]) -> Proc I O -> Prop) s (p : Proc I O) : Prop :=
  forall i, dis IRel l i -> exists p', reduceI p i p' /\ R s p'.

Definition Clause3 (I O : Ty) (IRel : cEquiv [I]) (l : level)
  (R : stream ([I] + [O]) -> Proc I O -> Prop) s (p : Proc I O) : Prop :=
  forall i s', s = scons (inl i) s' ->
               forall i', rel IRel l i' i -> exists p', reduceI p i' p' /\ R s' p'.

Definition Clause4 (I O : Ty) (ORel : cEquiv [O]) (l : level)
  (R : stream ([I] + [O]) -> Proc I O -> Prop) s (p : Proc I O) : Prop :=
  forall o s', s = scons (inr o) s' ->
               exists o', rel ORel l o' o /\ exists p', reduceO p o' p' /\ R s' p'.

Variant SimulationF (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (l : level)
        (R : stream ([I] + [O]) -> Proc I O -> Prop) :
  stream ([I] + [O]) -> Proc I O -> Prop :=
| SI s p : Clause1 IRel l R s p -> Clause2 IRel l R s p ->
           Clause3 IRel l R s p -> Clause4 ORel l R s p ->
           SimulationF IRel ORel l R s p.

Lemma monotone_SimulationF : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) l,
    monotone2 (@SimulationF I O IRel ORel l).
Proof.
  intros I O IRel ORel l x0 x1 r r' IN LE. inv IN. constructor.
  - intros i s' Heq Hd. apply LE. eapply H; eauto.
  - intros i Hd. move: (H0 _ Hd) => [p' [Hr HR]]. exists p'. split; auto.
  - intros i s' Heq i' Hr. move: (H1 _ _ Heq _ Hr) => [p' [Hred HR]].
    exists p'. split; auto.
  - intros o s' Heq. move: (H2 _ _ Heq) => [o' [Hr [p' [Hred HR]]]].
    exists o'. split; auto. exists p'. split; auto.
Qed.
Hint Resolve monotone_SimulationF : paco.

Definition simulation (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (l : level)
  s (p : Proc I O) := paco2 (@SimulationF I O IRel ORel l) bot2 s p.

(* Definition 4. *)
Definition PNI (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O) :=
  forall l s, Performs s p -> simulation IRel ORel l s p.

(** ** Performing a stream, exactly and up to indistinguishability *)

Lemma Performs_STrace : forall (I O : Ty) (ORel : cEquiv [O]) l s (p : Proc I O),
    Performs s p -> STrace ORel l s p.
Proof.
  intros I O ORel l. pcofix CIH. intros s p H. punfold H.
  destruct H as [q i q' s0 Hred HR | q o q' s0 Hred HR]; pfold.
  - apply STR1 with (p':=q'). auto. right. apply CIH. pclearbot. auto.
  - apply STR2 with (o':=o) (p':=q'). auto. apply rel_eq. right. apply CIH.
    pclearbot. auto.
Qed.

Lemma simulation_STrace : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) l s (p : Proc I O),
    simulation IRel ORel l s p -> STrace ORel l s p.
Proof.
  intros I O IRel ORel l. pcofix CIH. intros s p H. punfold H.
  destruct H as [s0 q C1 C2 C3 C4]. destruct s0 as [[i|o] s0]; pfold.
  - move: (C3 _ _ Logic.eq_refl i (rel_eq IRel i l)) => [p' [Hred HR]].
    apply STR1 with (p':=p'). auto. right. apply CIH. pclearbot. auto.
  - move: (C4 _ _ Logic.eq_refl) => [o' [Hr [p' [Hred HR]]]].
    apply STR2 with (o':=o') (p':=p'). auto. auto. right. apply CIH.
    pclearbot. auto.
Qed.

(* The exact run of [p] along the labels of [s]: the inputs of [s] are kept and
   its outputs are replaced by the ones [p] actually emits. *)
CoFixpoint runS (I O : Ty) (p : Proc I O) (s : stream ([I] + [O])) : stream ([I] + [O]) :=
  match shd s with
  | inl i => scons (inl i) (runS (stepI p i) (stl s))
  | inr _ => scons (inr (stepO p).1) (runS (stepO p).2 (stl s))
  end.

Lemma runS_Performs : forall (I O : Ty) (p : Proc I O) s, Performs (runS p s) p.
Proof.
  intros I O. pcofix CIH. intros p s. rewrite (sunfoldE (runS p s)). simpl.
  destruct (shd s) as [i|o]; pfold.
  - apply PF1 with (p':=stepI p i). apply reduceI_step. right. apply CIH.
  - apply PF2 with (p':=(stepO p).2). apply reduceO_step. right. apply CIH.
Qed.

(* Two streams with the same inputs and indistinguishable outputs. *)
Variant SRelF (I O : Ty) (ORel : cEquiv [O]) (l : level)
        (R : stream ([I] + [O]) -> stream ([I] + [O]) -> Prop) :
  stream ([I] + [O]) -> stream ([I] + [O]) -> Prop :=
| SRI i s s' : R s s' -> SRelF ORel l R (scons (inl i) s) (scons (inl i) s')
| SRO o o' s s' : rel ORel l o o' -> R s s' ->
                  SRelF ORel l R (scons (inr o) s) (scons (inr o') s').

Lemma monotone_SRelF : forall (I O : Ty) (ORel : cEquiv [O]) l,
    monotone2 (@SRelF I O ORel l).
Proof. intros I O ORel l x0 x1 r r' IN LE. inv IN; econstructor; eauto. Qed.
Hint Resolve monotone_SRelF : paco.

Definition SRel (I O : Ty) (ORel : cEquiv [O]) (l : level)
  (s s' : stream ([I] + [O])) := paco2 (@SRelF I O ORel l) bot2 s s'.

Lemma runS_SRel : forall (I O : Ty) (ORel : cEquiv [O]) l s (p : Proc I O),
    STrace ORel l s p -> SRel ORel l (runS p s) s.
Proof.
  intros I O ORel l. pcofix CIH. intros s p H. punfold H.
  destruct H as [q i q' s0 Hred HR | q o' o q' s0 Hred Hrel HR];
    rewrite (sunfoldE (runS q _)); simpl; pfold.
  - move: (reduceI_det Hred) => Heq. apply SRI. right. apply CIH.
    rewrite -Heq. pclearbot. eauto.
  - move: (reduceO_det Hred) => Heq. apply SRO.
    rewrite -Heq. simpl. auto.
    right. apply CIH. rewrite -Heq. simpl. pclearbot. eauto.
Qed.

Lemma SimulationF_inv : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) l R s (p : Proc I O),
    SimulationF IRel ORel l R s p ->
    Clause1 IRel l R s p /\ Clause2 IRel l R s p /\
    Clause3 IRel l R s p /\ Clause4 ORel l R s p.
Proof. intros I O IRel ORel l R s p H. destruct H. auto. Qed.

Lemma simulation_SRel : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) l s0 s (p : Proc I O),
    SRel ORel l s0 s -> simulation IRel ORel l s0 p -> simulation IRel ORel l s p.
Proof.
  intros I O IRel ORel l. pcofix CIH. intros s0 s p HR Hsim.
  punfold Hsim. move: (SimulationF_inv Hsim) => [C1 [C2 [C3 C4]]]. clear Hsim.
  punfold HR. destruct HR as [i sa sb HRt | o o1 sa sb Hro HRt]; pfold; constructor.
  - intros i0 s' Heq Hd. inversion Heq; subst. right. apply CIH with (s0:=sa).
    pclearbot. auto.
    move: (C1 _ _ Logic.eq_refl Hd). intros [X|X]; [auto | destruct X].
  - intros i0 Hd. move: (C2 _ Hd) => [p' [Hred HRp]]. exists p'. split. auto.
    right. apply CIH with (s0:=scons (inl i) sa).
    pfold. apply SRI. left. pclearbot. auto.
    pclearbot. auto.
  - intros i0 s' Heq i' Hr. inversion Heq; subst.
    move: (C3 _ _ Logic.eq_refl _ Hr) => [p' [Hred HRp]]. exists p'. split. auto.
    right. apply CIH with (s0:=sa). pclearbot. auto. pclearbot. auto.
  - intros o s' Heq. inversion Heq.
  - intros i0 s' Heq. inversion Heq.
  - intros i0 Hd. move: (C2 _ Hd) => [p' [Hred HRp]]. exists p'. split. auto.
    right. apply CIH with (s0:=scons (inr o) sa).
    pfold. apply SRO. auto. left. pclearbot. auto.
    pclearbot. auto.
  - intros i0 s' Heq. inversion Heq.
  - intros o2 s' Heq. inversion Heq; subst.
    move: (C4 _ _ Logic.eq_refl) => [o3 [Hr3 [p' [Hred HRp]]]].
    exists o3. split. eapply rel_trans; eauto. exists p'. split. auto.
    right. apply CIH with (s0:=sa). pclearbot. auto. pclearbot. auto.
Qed.

(** ** From the positional clauses to the simulation *)

Lemma sapp_cat : forall (A : Set) (t t' : seq A) (s : stream A),
    sapp (t ++ t') s = sapp t (sapp t' s).
Proof. induction t; intros; simpl; auto. rewrite IHt //. Qed.

Lemma sapp_scons : forall (A : Set) (t : seq A) a (s : stream A),
    sapp t (scons a s) = sinsert (size t) a (sapp t s).
Proof. induction t; intros; simpl; auto. rewrite IHt //. Qed.

Lemma runT_cat : forall (I O : Ty) (t t' : seq ([I] + [O])) (p : Proc I O),
    runT (t ++ t') p = runT t' (runT t p).
Proof. induction t as [|[i|o] t IH]; intros; simpl; auto. Qed.

Lemma STrace_sapp : forall (I O : Ty) (ORel : cEquiv [O]) l t s (p : Proc I O),
    STrace ORel l (sapp t s) p -> STrace ORel l s (runT t p).
Proof.
  intros I O ORel l t. induction t as [|[i|o] t IH]; intros s p H; simpl; auto.
  - punfold H. inv H. apply IH.
    match goal with Hr : reduceI _ _ _ |- _ => move: (reduceI_det Hr) => Heq end.
    rewrite -Heq. pclearbot. auto.
  - punfold H. inv H. apply IH.
    match goal with Hr : reduceO _ _ _ |- _ => move: (reduceO_det Hr) => Heq end.
    rewrite -Heq. simpl. pclearbot. auto.
Qed.

Lemma STrace_scons_out : forall (I O : Ty) (ORel : cEquiv [O]) l o s (p : Proc I O),
    STrace ORel l (scons (inr o) s) p ->
    rel ORel l (stepO p).1 o /\ STrace ORel l s (stepO p).2.
Proof.
  intros I O ORel l o s p H. punfold H. inv H.
  match goal with Hr : reduceO _ _ _ |- _ => move: (reduceO_det Hr) => Heq end.
  rewrite -Heq. simpl. split. auto. pclearbot. auto.
Qed.

(* The positional clauses give the simulation.  The pair carried along the
   coinduction is a run [t] of [p] and the stream left to perform: closure at
   position [n] in [p] is closure at the head of the residual after [n] steps. *)
Lemma SNI_simulation : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) l (p : Proc I O),
    SNI_l IRel ORel l p ->
    forall t s, STrace ORel l (sapp t s) p -> simulation IRel ORel l s (runT t p).
Proof.
  intros I O IRel ORel l p HSNI. move: (HSNI) => [Hsub [Hins Hdel]].
  pcofix CIH. intros t s HT. pfold. constructor.
  - intros i s' Heq Hd. subst. right. apply CIH.
    apply (Hdel _ i (size t)) => //. rewrite -sapp_scons. auto.
  - intros i Hd. exists (runT (t ++ [:: inl i]) p). split.
    rewrite runT_cat. simpl. apply reduceI_step.
    right. apply CIH. rewrite sapp_cat. simpl. rewrite sapp_scons.
    apply Hins => //.
  - intros i s' Heq i' Hr. subst. exists (runT (t ++ [:: inl i']) p). split.
    rewrite runT_cat. simpl. apply reduceI_step.
    right. apply CIH. rewrite sapp_cat. simpl. rewrite sapp_scons.
    apply (Hsub _ i i' (size t)). apply rel_sym. auto.
    rewrite -sapp_scons. auto.
  - intros o s' Heq. subst.
    move: (STrace_scons_out (STrace_sapp HT)) => [Hr HT'].
    exists (stepO (runT t p)).1. split. auto.
    exists (stepO (runT t p)).2. split. apply reduceO_step.
    have Hrt : (stepO (runT t p)).2 = runT (t ++ [:: inr o]) p.
    { rewrite runT_cat //. }
    rewrite Hrt. right. apply CIH. rewrite sapp_cat. simpl. auto.
Qed.

Theorem PNI_of_SNI : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O),
    SNI IRel ORel p -> PNI IRel ORel p.
Proof.
  intros I O IRel ORel p H l s HP.
  apply SNI_simulation with (t:=[::]). apply (H l). simpl.
  apply Performs_STrace. auto.
Qed.

(** ** From the simulation to the positional clauses *)

(* [p] simulates every stream it performs, so it simulates every stream it
   performs up to indistinguishability. *)
Lemma STrace_simulation : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O) l s,
    PNI IRel ORel p -> STrace ORel l s p -> simulation IRel ORel l s p.
Proof.
  intros I O IRel ORel p l s H HT.
  apply simulation_SRel with (s0:=runS p s). apply runS_SRel. auto.
  apply H. apply runS_Performs.
Qed.

(* Position [n] reduces to the head by peeling [n] labels: at each one the
   simulation hands back a step and a residual simulation. *)
Lemma simulation_sub_n : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) l n s (p : Proc I O) i i',
    rel IRel l i i' -> simulation IRel ORel l (sinsert n (inl i) s) p ->
    STrace ORel l (sinsert n (inl i') s) p.
Proof.
  intros I O IRel ORel l n. induction n as [|n IH]; intros s p i i' Hr Hsim; simpl.
  - punfold Hsim. move: (SimulationF_inv Hsim) => [C1 [C2 [C3 C4]]].
    move: (C3 _ _ Logic.eq_refl i' (rel_sym Hr)) => [p' [Hred HRp]].
    pfold. apply STR1 with (p':=p'). auto. left. apply (simulation_STrace (IRel:=IRel)).
    pclearbot. auto.
  - destruct s as [[j|o] s]; simpl in *; punfold Hsim;
      move: (SimulationF_inv Hsim) => [C1 [C2 [C3 C4]]].
    + move: (C3 _ _ Logic.eq_refl j (rel_eq IRel j l)) => [p' [Hred HRp]].
      pfold. apply STR1 with (p':=p'). auto. left. apply (IH _ _ i i') => //.
      pclearbot. auto.
    + move: (C4 _ _ Logic.eq_refl) => [o' [Hro [p' [Hred HRp]]]].
      pfold. apply STR2 with (o':=o') (p':=p'). auto. auto.
      left. apply (IH _ _ i i') => //. pclearbot. auto.
Qed.

Lemma simulation_ins_n : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) l n s (p : Proc I O) i,
    dis IRel l i -> simulation IRel ORel l s p ->
    STrace ORel l (sinsert n (inl i) s) p.
Proof.
  intros I O IRel ORel l n. induction n as [|n IH]; intros s p i Hd Hsim; simpl.
  - punfold Hsim. move: (SimulationF_inv Hsim) => [C1 [C2 [C3 C4]]].
    move: (C2 _ Hd) => [p' [Hred HRp]].
    pfold. apply STR1 with (p':=p'). auto. left. apply (simulation_STrace (IRel:=IRel)).
    pclearbot. auto.
  - destruct s as [[j|o] s]; simpl in *; punfold Hsim;
      move: (SimulationF_inv Hsim) => [C1 [C2 [C3 C4]]].
    + move: (C3 _ _ Logic.eq_refl j (rel_eq IRel j l)) => [p' [Hred HRp]].
      pfold. apply STR1 with (p':=p'). auto. left. apply (IH _ _ i) => //.
      pclearbot. auto.
    + move: (C4 _ _ Logic.eq_refl) => [o' [Hro [p' [Hred HRp]]]].
      pfold. apply STR2 with (o':=o') (p':=p'). auto. auto.
      left. apply (IH _ _ i) => //. pclearbot. auto.
Qed.

Lemma simulation_del_n : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) l n s (p : Proc I O) i,
    dis IRel l i -> simulation IRel ORel l (sinsert n (inl i) s) p ->
    STrace ORel l s p.
Proof.
  intros I O IRel ORel l n. induction n as [|n IH]; intros s p i Hd Hsim; simpl in *.
  - punfold Hsim. move: (SimulationF_inv Hsim) => [C1 [C2 [C3 C4]]].
    apply (simulation_STrace (IRel:=IRel)). move: (C1 _ _ Logic.eq_refl Hd). intros [X|X].
    auto. destruct X.
  - destruct s as [[j|o] s]; simpl in *; punfold Hsim;
      move: (SimulationF_inv Hsim) => [C1 [C2 [C3 C4]]].
    + move: (C3 _ _ Logic.eq_refl j (rel_eq IRel j l)) => [p' [Hred HRp]].
      pfold. apply STR1 with (p':=p'). auto. left. apply (IH _ _ i) => //.
      pclearbot. auto.
    + move: (C4 _ _ Logic.eq_refl) => [o' [Hro [p' [Hred HRp]]]].
      pfold. apply STR2 with (o':=o') (p':=p'). auto. auto.
      left. apply (IH _ _ i) => //. pclearbot. auto.
Qed.

Theorem SNI_of_PNI : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O),
    PNI IRel ORel p -> SNI IRel ORel p.
Proof.
  intros I O IRel ORel p H l. split; [|split].
  - intros s i i' n Hr HT. apply simulation_sub_n with (IRel:=IRel) (i:=i) => //.
    apply STrace_simulation => //.
  - intros s i n Hd HT. apply simulation_ins_n with (IRel:=IRel) => //.
    apply STrace_simulation => //.
  - intros s i n Hd HT. apply simulation_del_n with (IRel:=IRel) (n:=n) (i:=i) => //.
    apply STrace_simulation => //.
Qed.

(* Definition 4 and the definition used here hold of the same processes. *)
Theorem NI_paper : forall (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O),
    PNI IRel ORel p <-> NI IRel ORel p.
Proof.
  intros. split; intros H.
  - apply NI_of_SNI. apply SNI_of_PNI. auto.
  - apply PNI_of_SNI. apply SNI_of_NI. auto.
Qed.
