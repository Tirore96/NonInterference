Global Set Warnings "-all".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import RelationClasses.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
From HB Require Import structures.
From deriving Require Import deriving.
Require Import Stdlib.Classes.DecidableClass.
From Stdlib Require Eqdep_dec.

Import Order.TTheory.
Open Scope order_scope.

Variable d : Order.disp_t.
Variable L : bPOrderType d.

(*Possible instantiations of L are bool, nat, etc...*)
Definition level := L.

Ltac con := constructor.
Ltac econ := econstructor.
Ltac inv H := inversion H;subst.
Ltac econs := try do ? econ; done.
                     
Ltac split_ando :=
  intros;
   repeat
    match goal with
    | H:is_true (_ && _) |- _ => destruct (andP H); clear H    | H:_ && _ = true |- _ => destruct (andP H); clear H
    | H:_ /\ _ |- _ => destruct H
    | |- _ /\ _ => con
    | |- is_true (_ && _) => apply /andP ; con
    | |- is_true (_ || _) => apply /orP
    | H : ex _ |- _ => destruct H
    end; auto.


Ltac split_and :=
  intros;
   repeat
    match goal with
    | H:is_true (_ && _) |- _ => destruct (andP H); clear H
    | H:_ && _ = true |- _ => destruct (andP H); clear H
    | H:_ /\ _ |- _ => destruct H
    | |- _ /\ _ => con
    | |- is_true (_ && _) => apply /andP ; con
    | H : ex _ |- _ => destruct H
    end; auto;subst.


Ltac ssa' := rewrite ?inE;simpl in *; split_and;try done.
Ltac ssa := rewrite ?inE;simpl in *; split_ando;try done.

Ltac de i := destruct i;ssa.

Ltac case_if := match goal with 
                | [ |- context[if ?X then _ else _ ]] => have : X by subst
                | [ |- context[if ?X then _ else _ ]] => have : X = false by subst 

                | [ |- context[if ?X then _ else _ ]] => let H := fresh in destruct X eqn:H

                end; try (move=>->).

Definition order (b1 b2 : level) := b1 <= b2.


(* A characterised equivalence on [A].  At each level, [rel l] is an equivalence,
   so it partitions [A] into classes an observer at that level cannot tell apart,
   and the last field characterises [dis l] as one of those classes, the
   distinguished class, which is empty when the level hides nothing.  Both
   fields weaken downwards: a lower observer sees less.
   Paper: Section II-B. *)
Record cEquiv (A : Set) :=
        CEquiv {
           dis : level -> A -> Prop;
           rel : level -> A -> A -> Prop;
           equiv : forall l, Equivalence (rel l);
           _ : forall l0 l1, order l0 l1 ->
                             forall a0 a1, rel l1 a0 a1 -> rel l0 a0 a1;
           _ : forall l0 l1, order l0 l1 ->
                             forall a, dis l1 a -> dis l0 a;
            _: forall l a0, dis l a0 -> forall a1, dis l a1 <-> rel l a0 a1
          }.

Inductive Interrupt := DiskInterrupt | TimerInterrupt.
Inductive HandlerOutput := Nothing | Notify.
Inductive TypeSyscall := Syscall | Idle.
Inductive PublicOutput := GetRequest | Public_NOP.

Definition Interrupt_indDef := [indDef for Interrupt_rect].
Canonical Interrupt_indType := IndType Interrupt Interrupt_indDef.
Definition Interrupt_hasDecEq := [derive hasDecEq for Interrupt].
HB.instance Definition _ := Interrupt_hasDecEq.

Definition HandlerOutput_indDef := [indDef for HandlerOutput_rect].
Canonical HandlerOutput_indType := IndType HandlerOutput HandlerOutput_indDef.
Definition HandlerOutput_hasDecEq := [derive hasDecEq for HandlerOutput].
HB.instance Definition _ := HandlerOutput_hasDecEq.

Definition TypeSyscall_indDef := [indDef for TypeSyscall_rect].
Canonical TypeSyscall_indType := IndType TypeSyscall TypeSyscall_indDef.
Definition TypeSyscall_hasDecEq := [derive hasDecEq for TypeSyscall].
HB.instance Definition _ := TypeSyscall_hasDecEq.

Definition PublicOutput_indDef := [indDef for PublicOutput_rect].
Canonical PublicOutput_indType := IndType PublicOutput PublicOutput_indDef.
Definition PublicOutput_hasDecEq := [derive hasDecEq for PublicOutput].
HB.instance Definition _ := PublicOutput_hasDecEq.

Inductive Ty : Set := Nat | Times : Ty -> Ty -> Ty | Bool
                 | Option : Ty -> Ty | Sum : Ty -> Ty -> Ty
                 | TTypeSyscall | Unit
                 | TInterrupt | THandlerOutput |  TPublicOutput
                 | Empty. 

(*Derive NoConfusion for Ty.
Derive EqDec for Ty.*)

Definition Ty_indDef := [indDef for Ty_rect].
Canonical Ty_indType := IndType Ty Ty_indDef.
Definition Ty_hasDecEq := [derive hasDecEq for Ty].
HB.instance Definition _ := Ty_hasDecEq.

(* Dependent pairs over [Ty] are injective without any axiom, since [Ty] has
   decidable equality (Hedberg). *)
Lemma Ty_eq_dec (x y : Ty) : {x = y} + {x <> y}.
Proof. case: (x =P y); by [left | right]. Qed.

Lemma inj_pair2_Ty (P : Ty -> Type) (x : Ty) (p q : P x) :
  existT P x p = existT P x q -> p = q.
Proof. apply: Eqdep_dec.inj_pair2_eq_dec. exact: Ty_eq_dec. Qed.

Fixpoint interp (t : Ty) : Set :=
  match t with
  | Nat => nat
  | Times t0 t1 => (interp t0) * (interp t1)
  | Bool => bool
  | Option t' => option (interp t')
  | Sum t0 t1 => (interp t0) + (interp t1)            
  | TTypeSyscall => TypeSyscall
  | Unit => unit                     
  | TInterrupt => Interrupt
  | THandlerOutput => HandlerOutput
  | TPublicOutput => PublicOutput
  | Empty => Empty_set
  end.
Notation "[ i ]" := (interp i).

(** Process type **)
Inductive Proc : Ty -> Ty -> Set :=
| out  : forall {I O : Ty}, interp O -> Proc I O  
| map   : forall {I I' O O' : Ty}, (interp I -> interp I') -> (interp O -> interp O') -> Proc I' O -> Proc I O'
| sta   : forall {I O V :Ty}, (interp I -> interp V -> interp V) -> (interp O -> interp V -> interp V) -> interp V -> Proc (Times V I) O -> Proc I (Times V O)
| swi   : forall {I O : Ty},  bool -> Proc I (Times Bool O)%type -> Proc ((Times Bool I)) (Option O)
| par   : forall {I O1 O2: Ty}, Proc I O1 -> Proc I O2 -> Proc I (Times O1 O2)
| loop  : forall {I : Ty}, Proc I I -> Proc I I
| maybe : forall {I O: Ty}, Proc I O -> Proc (Option I) O.
Arguments out {_} {_} o.

Definition xor (b1 b2 : bool) := (Datatypes.negb (b1 == b2)).

Lemma xorK : forall x y, xor (xor x y) y = x.
Proof. by destruct x, y. Qed.

Lemma xorC : forall x y, xor x y = xor y x.
Proof. by destruct x, y. Qed.

Lemma xorFalse : forall x, xor x false = x.
Proof. by destruct x. Qed.

Lemma xorTrue : forall x, xor x true = negb x.
Proof. by destruct x. Qed.

Inductive reduceI : forall (I O : Ty), Proc I O -> interp I -> Proc I O -> Prop :=
| reduce_outI I O i (o : [O]) : reduceI ( @out I _ o) i ( @out I _ o)
| reduce_mapI (I I' O O' : Ty) p p' i i' (f : [I] -> [I']) (g : [O] -> [O']) : f i = i' -> reduceI p i' p' -> reduceI (map f g p) i (map f g p')
| reduce_staI (V I O : Ty) v v' (p : Proc (Times V I) O) p' i (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) : f i v = v' -> reduceI p (v', i) p' -> reduceI (sta f g v p) i (sta f g v' p')
| reduce_swiI (I O : Ty) b b' b'' (p : Proc I (Times Bool O)) p' (i : [I]) : b'' = xor b b' -> reduceI p i p' -> reduceI (swi b p) (b', i) (swi b'' p')
| reduce_maybeI (I O : Ty) (p : Proc I O) : reduceI (maybe p) None (maybe p)
| reduce_maybeI2 (I O : Ty) (p p' : Proc I O) (i : [I]) : reduceI p i p' -> reduceI (maybe p) (Some i) (maybe p')
| reduce_parI (I O1 O2 : Ty) (p1 p1' : Proc I O1) (p2 p2' : Proc I O2) (i : [I]) : reduceI p1 i p1' -> reduceI p2 i p2' -> reduceI (par p1 p2) i (par p1' p2')
| reduce_loopI (I :Ty) (p p' : Proc I I) (i : [I]) : reduceI p i p' -> reduceI (loop p) i (loop p').

Hint Constructors reduceI : core.

Inductive reduceO : forall (I O : Ty), Proc I O -> [O] -> Proc I O -> Prop :=
| reduce_outO (I O : Ty) (o : [O]) : reduceO ( @out I _ o) o ( @out I _ o)
| reduce_mapO (I I' O O' : Ty) p p' o o' (f : [I] -> [I']) (g : [O] ->  [O']) : g o = o' -> reduceO p o p' -> reduceO (map f g p) o' (map f g p')
| reduce_staO (V I O : Ty) v v' p p' o (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) : g o v = v' -> reduceO p o p' -> reduceO (sta f g v p) (v', o) (sta f g v' p')
| reduce_swiO (I O : Ty) (p : Proc I (Times Bool O)): reduceO (swi false p) None (swi false p)
| reduce_swiO2 (I O : Ty) b b' (p : Proc I (Times Bool O)) p' (o : [O]) : b' = xor true b -> reduceO p (b, o) p' -> reduceO (swi true p) (Some o) (swi b' p')
| reduce_maybeO (I O : Ty) (p p' : Proc I O) (o : [O]) : reduceO p o p' -> reduceO (maybe p) o (maybe p')
| reduce_parO (I O1 O2 : Ty) (p1 p1' : Proc I O1) (p2 p2' : Proc I O2) (o : [O1]) (o' : [O2]) : reduceO p1 o p1' -> reduceO p2 o' p2' -> reduceO (par p1 p2) (o, o') (par p1' p2')
| reduce_loopO (O :Ty) (p p' p'' : Proc O O) (o : [O]) : reduceO p o p' -> reduceI p' o p'' -> reduceO (loop p) o (loop p'').
Hint Constructors reduceO : core.

(* Reduction as functions.  Every process can take an input step and an output
   step, and [stepI] / [stepO] compute them. *)
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

(* Reduction is deterministic: it agrees with [stepI] and [stepO]. *)
Lemma reduceI_fun : forall (I O : Ty) (p : Proc I O) i p',
    reduceI p i p' -> p' = stepI p i.
Proof.
  intros I O p i p' H. induction H; simpl; subst.
  all: try rewrite IHreduceI.
  all: try rewrite IHreduceI1.
  all: try rewrite IHreduceI2.
  all: reflexivity.
Qed.

Lemma reduceO_fun : forall (I O : Ty) (p : Proc I O) o p',
    reduceO p o p' -> (o,p') = stepO p.
Proof.
  intros I O p o p' H. induction H; simpl; subst.
  all: try (apply reduceI_fun in H0; subst).
  all: try rewrite -IHreduceO.
  all: try rewrite -IHreduceO1.
  all: try rewrite -IHreduceO2.
  all: reflexivity.
Qed.

(* Inversion of a reduction, one lemma per rule.  The relations are indexed by
   the input and output types, so [inversion] and [dependent destruction] on
   them need injectivity of dependent pairs, and with it the axiom
   [eq_rect_eq].  These lemmas go through determinism instead and use no axiom.
   Each states the premises of its rule, as [dependent destruction] would. *)
Section Inversion.
Implicit Types (I O V : Ty).

Lemma inv_outI I O (o : [O]) i p' : reduceI (@out I O o) i p' -> p' = out o.
Proof. by move/reduceI_fun. Qed.

Lemma inv_mapI (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) p i p' :
  reduceI (map f g p) i p' -> exists i' q, f i = i' /\ reduceI p i' q /\ p' = map f g q.
Proof. move/reduceI_fun => ->. exists (f i), (stepI p (f i)). split => //. split => //. exact: reduceI_step. Qed.

Lemma inv_staI I O V (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) v p i p' :
  reduceI (sta f g v p) i p' -> exists v' q, f i v = v' /\ reduceI p (v', i) q /\ p' = sta f g v' q.
Proof. move/reduceI_fun => ->. exists (f i v), (stepI p (f i v, i)). split => //. split => //. exact: reduceI_step. Qed.

Lemma inv_swiI I O b (p : Proc I (Times Bool O)) b' (i : [I]) p' :
  reduceI (swi b p) (b', i) p' -> exists b'' q, b'' = xor b b' /\ reduceI p i q /\ p' = swi b'' q.
Proof. move/reduceI_fun => ->. exists (xor b b'), (stepI p i). split => //. split => //. exact: reduceI_step. Qed.

Lemma inv_maybeI_None I O (p : Proc I O) p' : reduceI (maybe p) None p' -> p' = maybe p.
Proof. by move/reduceI_fun. Qed.

Lemma inv_maybeI_Some I O (p : Proc I O) (i : [I]) p' :
  reduceI (maybe p) (Some i) p' -> exists q, reduceI p i q /\ p' = maybe q.
Proof. move/reduceI_fun => ->. exists (stepI p i). split => //. exact: reduceI_step. Qed.

Lemma inv_parI I O1 O2 (p1 : Proc I O1) (p2 : Proc I O2) i p' :
  reduceI (par p1 p2) i p' -> exists q1 q2, reduceI p1 i q1 /\ reduceI p2 i q2 /\ p' = par q1 q2.
Proof. move/reduceI_fun => ->. exists (stepI p1 i), (stepI p2 i). split; [exact: reduceI_step | split; [exact: reduceI_step | done]]. Qed.

Lemma inv_loopI I (p : Proc I I) i p' :
  reduceI (loop p) i p' -> exists q, reduceI p i q /\ p' = loop q.
Proof. move/reduceI_fun => ->. exists (stepI p i). split => //. exact: reduceI_step. Qed.

Lemma inv_outO I O (o : [O]) o' p' : reduceO (@out I O o) o' p' -> o' = o /\ p' = out o.
Proof. by move/reduceO_fun => /= [-> ->]. Qed.

Lemma inv_mapO (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) p o' p' :
  reduceO (map f g p) o' p' -> exists q o, g o = o' /\ reduceO p o q /\ p' = map f g q.
Proof.
  move/reduceO_fun => /=. move: (reduceO_step p). case: (stepO p) => o q /= Hs [-> ->].
  by exists q, o.
Qed.

Lemma inv_staO I O V (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) v p o' p' :
  reduceO (sta f g v p) o' p' ->
  exists v' q o, g o v = v' /\ reduceO p o q /\ o' = (v', o) /\ p' = sta f g v' q.
Proof.
  move/reduceO_fun => /=. move: (reduceO_step p). case: (stepO p) => o q /= Hs [-> ->].
  by exists (g o v), q, o.
Qed.

Lemma inv_swiO_false I O (p : Proc I (Times Bool O)) o' p' :
  reduceO (swi false p) o' p' -> o' = None /\ p' = swi false p.
Proof. by move/reduceO_fun => /= [-> ->]. Qed.

Lemma inv_swiO_true I O (p : Proc I (Times Bool O)) o' p' :
  reduceO (swi true p) o' p' ->
  exists b b' q o, b' = xor true b /\ reduceO p (b, o) q /\ o' = Some o /\ p' = swi b' q.
Proof.
  move/reduceO_fun => /=. move: (reduceO_step p). case: (stepO p) => [[b o] q] /= Hs [-> ->].
  by exists b, (xor true b), q, o.
Qed.

Lemma inv_maybeO I O (p : Proc I O) o' p' :
  reduceO (maybe p) o' p' -> exists q, reduceO p o' q /\ p' = maybe q.
Proof.
  move/reduceO_fun => /=. move: (reduceO_step p). case: (stepO p) => o q /= Hs [-> ->].
  by exists q.
Qed.

Lemma inv_parO I O1 O2 (p1 : Proc I O1) (p2 : Proc I O2) o' p' :
  reduceO (par p1 p2) o' p' ->
  exists q1 q2 o1 o2, reduceO p1 o1 q1 /\ reduceO p2 o2 q2 /\ o' = (o1, o2) /\ p' = par q1 q2.
Proof.
  move/reduceO_fun => /=. move: (reduceO_step p1) (reduceO_step p2).
  case: (stepO p1) => o1 q1 /= H1. case: (stepO p2) => o2 q2 /= H2 [-> ->].
  by exists q1, q2, o1, o2.
Qed.

Lemma inv_loopO I (p : Proc I I) o' p' :
  reduceO (loop p) o' p' -> exists q q', reduceO p o' q /\ reduceI q o' q' /\ p' = loop q'.
Proof.
  move/reduceO_fun => /=. move: (reduceO_step p). case: (stepO p) => o q /= Hs [-> ->].
  exists q, (stepI q o). split => //. split => //. exact: reduceI_step.
Qed.
End Inversion.

(* Case analysis with the cases in the order of the reduction rules. *)
Lemma option_rule_order (A : Type) (P : option A -> Prop) :
  P None -> (forall a, P (Some a)) -> forall o, P o.
Proof. by move=> ? ? []. Qed.

Lemma bool_rule_order (P : bool -> Prop) : P false -> P true -> forall b, P b.
Proof. by move=> ? ? []. Qed.

(* Use an equation produced by an inversion lemma: substitute a variable side,
   split an equation between pairs or options, or close the goal when the two
   sides start with different constructors. *)
Ltac use_eq E :=
  match type of E with
  | ?a = ?b =>
    first [ is_var a; subst a
          | is_var b; subst b
          | discriminate E
          | (injection E; clear E;
             repeat (let E' := fresh "E" in intro E'; use_eq E'))
          | idtac ]
  end.

(* Invert one reduction hypothesis whose process is a constructor term. *)
Ltac inv_red H :=
  match type of H with
  | reduceI (out _) _ _ => apply inv_outI in H; use_eq H
  | reduceI (map _ _ _) _ _ =>
      apply inv_mapI in H; let E1 := fresh "E" in let E2 := fresh "E" in
      destruct H as (? & ? & E1 & H & E2); use_eq E2; use_eq E1
  | reduceI (sta _ _ _ _) _ _ =>
      apply inv_staI in H; let E1 := fresh "E" in let E2 := fresh "E" in
      destruct H as (? & ? & E1 & H & E2); use_eq E2; use_eq E1
  | reduceI (swi _ _) (_, _) _ =>
      apply inv_swiI in H; let E1 := fresh "E" in let E2 := fresh "E" in
      destruct H as (? & ? & E1 & H & E2); use_eq E2; use_eq E1
  | reduceI (swi _ _) ?x _ => split_scrutinee H x
  | reduceI (maybe _) None _ => apply inv_maybeI_None in H; use_eq H
  | reduceI (maybe _) (Some _) _ =>
      apply inv_maybeI_Some in H; let E := fresh "E" in
      destruct H as (? & H & E); use_eq E
  | reduceI (maybe _) ?x _ => split_scrutinee H x
  | reduceI (par _ _) _ _ =>
      apply inv_parI in H; let H2 := fresh "H" in let E := fresh "E" in
      destruct H as (? & ? & H & H2 & E); use_eq E
  | reduceI (loop _) _ _ =>
      apply inv_loopI in H; let E := fresh "E" in destruct H as (? & H & E); use_eq E
  | reduceO (out _) _ _ =>
      apply inv_outO in H; let E := fresh "E" in destruct H as [H E]; use_eq E; use_eq H
  | reduceO (map _ _ _) _ _ =>
      apply inv_mapO in H; let E1 := fresh "E" in let E2 := fresh "E" in
      destruct H as (? & ? & E1 & H & E2); use_eq E2; use_eq E1
  | reduceO (sta _ _ _ _) _ _ =>
      apply inv_staO in H; let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
      destruct H as (? & ? & ? & E1 & H & E2 & E3); use_eq E3; use_eq E2; use_eq E1
  | reduceO (swi true _) _ _ =>
      apply inv_swiO_true in H; let E1 := fresh "E" in let E2 := fresh "E" in
      let E3 := fresh "E" in
      destruct H as (? & ? & ? & ? & E1 & H & E2 & E3); use_eq E3; use_eq E2; use_eq E1
  | reduceO (swi false _) _ _ =>
      apply inv_swiO_false in H; let E := fresh "E" in
      destruct H as [H E]; use_eq E; use_eq H
  | reduceO (swi ?b _) _ _ => split_scrutinee H b
  | reduceO (maybe _) _ _ =>
      apply inv_maybeO in H; let E := fresh "E" in destruct H as (? & H & E); use_eq E
  | reduceO (par _ _) _ _ =>
      apply inv_parO in H; let H2 := fresh "H" in let E1 := fresh "E" in let E2 := fresh "E" in
      destruct H as (? & ? & ? & ? & H & H2 & E1 & E2); use_eq E2; use_eq E1
  | reduceO (loop _) _ _ =>
      apply inv_loopO in H; let H2 := fresh "H" in let E := fresh "E" in
      destruct H as (? & ? & H & H2 & E); use_eq E
  (* A defined process: unfold it to its head constructor first. *)
  | reduceI ?p _ _ =>
      let q := eval hnf in p in
      (tryif constr_eq p q then fail else change p with q in H; inv_red H)
  | reduceO ?p _ _ =>
      let q := eval hnf in p in
      (tryif constr_eq p q then fail else change p with q in H; inv_red H)
  end
(* A scrutinee that is not yet a constructor (a pair, an option, a boolean):
   evaluate it if it computes to one, and otherwise split on it, keeping an
   equation, as [dependent destruction] would.  The cases come in the order of
   the rules. *)
with split_scrutinee H x :=
  first
    [ is_var x; split_var H x
    | let x' := eval vm_compute in x in
      tryif constr_eq x x' then fail else (change x with x' in H; inv_red H)
    | let Ex := fresh "Ex" in destruct x eqn:Ex; inv_red H ]
(* Split a variable, with the cases in the order of the rules ([None] before
   [Some], [false] before [true]). *)
with split_var H x :=
  let T := type of x in let T := eval hnf in T in
  lazymatch T with
  | option _ => destruct x using option_rule_order; inv_red H
  | bool => destruct x using bool_rule_order; inv_red H
  | _ => destruct x; inv_red H
  end.


Ltac check_if_var x :=
  first [ is_var x;fail 1 "Term" x "is not a bare variable" | idtac ].

Ltac match_dd_once := 
    match goal with
    | H : reduceI ?p _ _ |- _ => check_if_var p; inv_red H
    | H : reduceO ?p _ _ |- _ => check_if_var p; inv_red H
    end.


Ltac match_dd := 
   repeat match_dd_once.

Ltac match_dd_o := 
   repeat (match_dd_once;eauto).

(* Invert every output step before any input step.  In a feedback loop the
   next input is computed from the last output, so inverting outputs first
   lets the input steps' arguments evaluate to constructors. *)
Ltac match_dd_out_first :=
  repeat (match goal with H : reduceO ?p _ _ |- _ => check_if_var p; inv_red H end);
  match_dd.


Inductive Trace (I O : Ty) (ORel : cEquiv [O]) (l : level) : list ([I] + [O]) -> Proc I O -> Prop :=
| TR0 p : Trace ORel l nil p
| TR1 p i p' t : reduceI p i p' -> Trace ORel l t p' -> Trace ORel l (inl i::t) p
| TR2 p o' o p' t : reduceO p o' p' -> rel ORel l o' o -> Trace ORel l t p' -> Trace ORel l (inr o::t) p.
Hint Constructors Trace.

Fixpoint insert (A : Set) (n : nat) (a : A) (l : seq A) :=
  match n with
  | 0 => a::l
  | n'.+1 => if l is a'::l' then a'::(insert n' a l') else nil
  end.

Fixpoint remove (A : Set) (n : nat) (l : seq A) :=
  match n with
  | 0 => if l is a::l' then l' else nil
  | n'.+1 => if l is a::l' then a::(remove n' l') else nil
  end.

Definition NI_l (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (l : level) (p : Proc I O) : Prop :=
  (forall t i i' n, rel IRel l i i' -> Trace ORel l (insert n (inl i) t) p -> Trace ORel l (insert n (inl i') t) p) /\
  (forall t i n, dis IRel l i -> Trace ORel l t p -> Trace ORel l (insert n (inl i) t) p) /\
  (forall t i n, dis IRel l i -> Trace ORel l (insert n (inl i) t) p -> Trace ORel l t p).


Definition NI (I O : Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (p : Proc I O) := forall l, NI_l IRel ORel l p.


Definition false_equiv : cEquiv ([Bool]).
  refine (@CEquiv _
            (fun l (b : [Bool]) => ~~ b /\ l = \bot)
            (fun l b1 b2 => b1 = b2)
            _
            _
            _
            _).
  intros. done.
  intros. ssa. subst. rewrite /order in H. rewrite lex0 in H. apply/eqP. done.
  intros. ssa. con. ssa. subst. de a1. de a0.
  intros. subst. ssa.
Defined.

Definition public_equiv (A : Ty) : cEquiv ([A]).
  refine (@CEquiv _
            (fun l b => False)
            (fun l b1 b2 => b1 = b2)
            _
            _
            _
            _).
intros.
done.
eauto.
eauto.
intros. done.
Defined.

Lemma order_bot : forall (l : level), order l \bot -> l = \bot.
Proof.
intros.
rewrite /order lex0 in H.
by apply/eqP.
Qed.


Lemma not_booleq : forall (A : eqType) (a : A), a != a -> False.
Proof.
intros.
move/eqP : H.
done.
Qed.
Hint Resolve not_booleq.

Definition private_equiv (A : Ty) : cEquiv ([A]).
  refine (@CEquiv _
            (fun l b => l = \bot)
            (fun l b1 b2 => l <> \bot /\ b1 = b2 \/ l = \bot)
            _
            _
            _
            _).
  - intros l. con. 
    + intro. destruct (eqVneq l \bot). auto.  left. split_and. intro. subst. rewrite eqxx in i. done.
    + intros x y. case. ssa. intros. subst. auto.
      intro. intros. destruct H. destruct H0. ssa. subst. auto. ssa. ssa.
      intros. de H0. subst.
      destruct (eqVneq l0 \bot). auto. left. split_and. intro. subst. rewrite eqxx in i. done.
      subst. apply order_bot in H. subst. auto.
      intros. subst. apply order_bot in H. subst. done.
      intros. subst. con. auto. auto.
Defined.


Lemma dis_rel_dis : forall (I : Ty) (IRel : cEquiv [I]) l x y, dis IRel l x -> rel IRel l x y -> dis IRel l y.
Proof.
  intros. de IRel. apply/i;eauto.
Qed.
Lemma dis_rel_dis2 : forall (I : Ty) (IRel : cEquiv [I]) l x y, dis IRel l x -> rel IRel l y x -> dis IRel l y.
Proof.
  intros. de IRel. apply/i;eauto.
  move:(equiv0 l)=> [] _ Hsym _. apply/Hsym. auto.
Qed.
Lemma dis_dis_rel : forall (I : Ty) (IRel : cEquiv [I]) l x y, dis IRel l x -> dis IRel l y -> rel IRel l x y.
Proof.
  intros. de IRel;eauto. apply/i;eauto.
Qed.


Hint Resolve dis_rel_dis dis_rel_dis2 dis_dis_rel.


Definition levelPred := level -> Prop.
Definition presP (P:levelPred) := forall x0 x1, order x0 x1 -> P x0 -> P x1.

Lemma rel_refl : forall (A : Ty) (ARel : cEquiv [A]) l x, rel ARel l x x.
Proof.
  intros. de ARel. move:(equiv0 l). case. eauto.
Qed.
Lemma rel_sym : forall A (ARel : cEquiv A) l x y, rel ARel l x y -> rel ARel l y x.
  Proof.
    intros. destruct ARel;ssa.
    move: (equiv0 l). case. ssa.
  Qed.

Lemma rel_trans : forall A (ARel : cEquiv A) l x y z, rel ARel l x y -> rel ARel l y z -> rel ARel l x z.
  Proof.
    intros. destruct ARel;ssa.
    move: (equiv0 l). case. ssa. eauto.
  Qed.

Lemma cEquiv_rule1 : forall (A : Ty) (ARel : cEquiv [A]) l0 l1, order l0 l1 -> forall a0 a1 : [A], rel ARel l1 a0 a1 -> rel ARel l0 a0 a1.
Proof. intros. de ARel. eauto.
Qed.

Lemma cEquiv_rule2 : forall (A : Ty) (ARel : cEquiv [A]), forall l0 l1 : level, order l0 l1 -> forall a : [A], dis ARel l1 a -> dis ARel l0 a.
Proof. intros. de ARel. eauto.
Qed.

Lemma cEquiv_rule3 : forall (A : Ty) (ARel : cEquiv [A]), forall (l : level) (a0 : [A]), dis ARel l a0 -> forall a1 : [A], dis ARel l a1 <-> rel ARel l a0 a1.
Proof. intros. de ARel. 
Qed.

Hint Resolve rel_refl rel_sym rel_trans cEquiv_rule1 cEquiv_rule2 cEquiv_rule3.

(* The four pair equivalences differ only in which component makes a pair
   unobservable.  Taking that predicate as a parameter forces the rest: two
   pairs are related componentwise, or by both being unobservable.  The four
   cEquiv obligations are then discharged once instead of four times. *)
Definition eqpair_aux {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O])
                      (D : level -> [Times I O] -> Prop) :
  (forall l0 l1, order l0 l1 -> forall x, D l1 x -> D l0 x) ->
  (forall l x y, D l x -> rel IRel l x.1 y.1 -> rel ORel l x.2 y.2 -> D l y) ->
  cEquiv ([Times I O]).
  move=> Hmon HD.
  refine (@CEquiv _ D
            (fun l x y => rel IRel l x.1 y.1 /\ rel ORel l x.2 y.2 \/
                          D l x /\ D l y)
            _ _ _ _).
  - move=> l. con.
    move=> x. left. ssa.
    move=> x y. case; ssa; eauto.
    move=> x y z. case; case=> Ha Hb; case; case=> Hc Hd;
      [left|right|right|right]; ssa; eauto; try (apply/(HD _ y); eauto).
  - move=> l0 l1 Hord x y. case; case=> Ha Hb; [left|right]; ssa; eauto.
  - exact Hmon.
  - move=> l x Hx y. con.
    move=> Hy. right. ssa.
    case. case=> Ha Hb. apply/(HD _ x); eauto. case. ssa.
Defined.

(* eqpair is left concrete on purpose.  It is the equivalence the models are built
   from, and going through eqpair_aux would leave every goal about it carrying a
   [\/ False /\ False] disjunct that no longer splits like a conjunction. *)
Definition eqpair {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O]) : cEquiv ([Times I O]).
  refine (@CEquiv _
            (fun (l : level) _ => False)
            (fun l io1 io2 => rel IRel l io1.1 io2.1 /\ rel ORel l io1.2 io2.2)
            _ _ _ _).
  - move=> l. con.
    move=> x. ssa.
    move=> x y. ssa; eauto.
    move=> x y z. ssa; eauto.
  - move=> l0 l1 Hord x y. ssa; eauto.
  - done.
  - ssa.
Defined.

Definition eqpair_L {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O]) : cEquiv ([Times I O]).
  apply:(@eqpair_aux _ _ IRel ORel (fun l io => dis IRel l io.1)); ssa; eauto.
Defined.

Definition eqpair_R {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O]) : cEquiv ([Times I O]).
  apply:(@eqpair_aux _ _ IRel ORel (fun l io => dis ORel l io.2)); ssa; eauto.
Defined.

Definition eqpair_LR {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O]) : cEquiv ([Times I O]).
  apply:(@eqpair_aux _ _ IRel ORel
           (fun l io => dis IRel l io.1 /\ dis ORel l io.2)); ssa; eauto.
Defined.

(* Both sum equivalences relate a Sum tag-by-tag and never relate an inl to an inr.
   They differ only in whether an inl can be unobservable, so that is the
   parameter; an inr never is.  The four cEquiv obligations are discharged once
   instead of twice. *)
Definition eqsum_aux {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O])
                     (D : level -> [I] -> Prop) :
  (forall l0 l1, order l0 l1 -> forall i, D l1 i -> D l0 i) ->
  (forall l i0, D l i0 -> forall i1, D l i1 <-> rel IRel l i0 i1) ->
  cEquiv ([Sum I O]).
  move=> Hmon Hl.
  assert (HlD : forall l i0 i1, D l i0 -> rel IRel l i0 i1 -> D l i1)
    by (intros; by apply/(Hl _ _ H)).
  assert (HlR : forall l i0 i1, D l i0 -> D l i1 -> rel IRel l i0 i1)
    by (intros; by apply/(Hl _ _ H)).
  refine (@CEquiv _
            (fun l x => match x with | inl i => D l i | inr _ => False end)
            (fun l x y => match x,y with
                          | inl i1,inl i2 => rel IRel l i1 i2
                          | inr o1,inr o2 => rel ORel l o1 o2
                          | _,_ => False
                          end)
            _ _ _ _).
  - move=> l. con.
    move=> x. de x.
    move=> x y. de x; de y; ssa; eauto.
    move=> x y z. de x; de y; de z; ssa; eauto.
  - move=> l0 l1 Hord x y. de x; de y; ssa; eauto.
  - move=> l0 l1 Hord x. de x. eauto.
  - move=> l x Hx y. de x; de y; con; ssa; eauto.
Defined.

Definition eqsum {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O]) : cEquiv ([Sum I O]).
  apply:(@eqsum_aux _ _ IRel ORel (fun l i => False)); ssa.
Defined.

Definition eqsum_L {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O]) : cEquiv ([Sum I O]).
  apply:(@eqsum_aux _ _ IRel ORel (dis IRel)); ssa; eauto.
Defined.


Definition eqmaybe_dis {V : Ty} (P: levelPred) (VRel : cEquiv [V]) l (v : [Option V]) := if v is Some v' then dis VRel l v' else ~ P l.
Definition eqmaybe {V : Ty} (P: levelPred) (VRel : cEquiv [V]) : presP P -> cEquiv ([Option V]).
intros.  
    refine (@CEquiv _
            (fun l v => eqmaybe_dis P VRel l v)
            (fun l b1 b2 => match b1,b2 with
                            | Some v1,Some v2 => rel VRel l v1 v2
                            | None, None => True
                            | _,_ => (eqmaybe_dis P VRel l b1) /\ (eqmaybe_dis P VRel l b2)
                            end)
            _
            _
            _
            _).
    intros. con.
    intro. de x.
    intro. intros. de x. de y.
    ssa. de y.
    intro. intros.
    de x. de y.
    de z. eauto. eauto. de z. 
    de y. de z. eauto.

    intros. de a0. de a1. eauto. eauto. eauto.
    
    de a1. eauto. eauto.

    intros. de VRel. de a. eauto. eauto.

    intros. con.

    intros. de a0.
    de a1. de a1.
    de a0. de a1. eauto. de a1.
Defined.    

Definition Option_presP_all : presP (fun _ => True).
  rewrite /presP. eauto.
Qed.

Definition aware (V : Ty) (VRel : cEquiv [V]) (v : [V]) : levelPred
  := fun l => (forall v', rel VRel l v v' -> v = v' /\ ~ dis VRel l v').

Definition Option_presP_aware (BRel : cEquiv [Bool]) : presP (fun l => aware BRel true l).
  rewrite /presP. intros. destruct BRel. move: H0. rewrite /aware. ssa.
  have: rel0 x0 true v'. eauto. move/H0. ssa.
  have: rel0 x0 true v'. eauto. move/H0. ssa. eauto.
Qed.


Definition Option_presP_nobody : presP (fun _ => False).
  rewrite /presP. eauto.
Qed.

Definition Option_presP_nonbot : presP (fun l => l <> \bot).
  rewrite /presP. intros. subst. rewrite /order in H. intro. subst. apply/H0.  rewrite lex0 in H. by apply/eqP.
Qed.

Definition eqmaybe_all {V : Ty} (VRel : cEquiv [V]) : cEquiv ([Option V]).
  apply:eqmaybe. apply VRel. apply: Option_presP_all.
Defined.

Definition eqmaybe_nonbot {V : Ty} (VRel : cEquiv [V]) : cEquiv ([Option V]).
  apply:eqmaybe. apply VRel. apply: Option_presP_nonbot.
Defined.

Definition eqmaybe_aware {V : Ty} (VRel : cEquiv [V]) (BRel : cEquiv [Bool]) : cEquiv ([Option V]).
  apply:eqmaybe. apply VRel. apply: Option_presP_aware. apply BRel.
Defined. 

Definition eqmaybe_nobody {V : Ty} (VRel : cEquiv [V]) : cEquiv ([Option V]).
  apply:eqmaybe. apply VRel. apply:Option_presP_nobody.
Defined. 

Lemma rel_eq : forall (I : Set) (IRel : cEquiv I) (x : I) l, rel IRel l x x.
Proof.
  intros. de IRel. ssa.
  move: (equiv0 l). case. move=> Hr _ _. apply Hr.
Qed.
Hint Resolve rel_eq.

(* [ObliviousTrace ORel l o0 s]: every output in [s] is indistinguishable from
   the reference output [o0] at level [l], so an observer there sees the same
   class throughout.  The reference is a plain output value, not a member of the
   distinguished class.  Used only by [oblivious_class] below. *)
Inductive ObliviousTrace {I O : Ty} (ORel : cEquiv [O]) (l : level) (o0 : [O]) : seq ([I] + [O]) -> Prop :=
 | OT_nil : ObliviousTrace ORel l o0 nil
 | OT_cons_in i s :  ObliviousTrace ORel l o0 s -> ObliviousTrace ORel l o0 ((inl i)::s)
 | OT_cons_out o s :  rel ORel l o0 o -> ObliviousTrace ORel l o0 s -> ObliviousTrace ORel l o0 ((inr o)::s).

Definition oblivious_at {I O : Ty} (ORel : cEquiv [O]) (o0 : [O]) (p : Proc I O) (l : level) :=
  forall s, Trace ORel l s p -> ObliviousTrace ORel l o0 s.

(* [p] never leaves one indistinguishability class at [l].  This is weaker than
   [oblivious] below and is used only inside the proof of [swi_NI]. *)
Definition oblivious_class {I O : Ty} (ORel : cEquiv [O]) (p : Proc I O) (l : level) :=
  exists o0, oblivious_at ORel o0 p l.

(* [DisTrace ORel l s]: every output in [s] is unobservable at [l]. *)
Inductive DisTrace {I O : Ty} (ORel : cEquiv [O]) (l : level) : seq ([I] + [O]) -> Prop :=
 | DT_nil : DisTrace ORel l nil
 | DT_cons_in i s : DisTrace ORel l s -> DisTrace ORel l ((inl i)::s)
 | DT_cons_out o s : dis ORel l o -> DisTrace ORel l s -> DisTrace ORel l ((inr o)::s).

(* Obliviousness as in Rafnsson et al.: every output [p] can emit is
   unobservable at [l]. *)
Definition oblivious {I O : Ty} (ORel : cEquiv [O]) (p : Proc I O) (l : level) :=
  forall s, Trace ORel l s p -> DisTrace ORel l s.

Definition aware_or_oblivious  {I O : Ty} (ORel : cEquiv [O]) (o : [O]) (p : Proc I O) : levelPred := fun l => aware ORel o l \/ oblivious ORel p l.


Lemma zerol : 0 < 0 = false.
Proof. done.
Qed.

Ltac swi_instans :=
   repeat
    match goal with
    | |- context [ swi (?x < ?x) _] => is_evar x; unify x 0; try rewrite zerol
    | |- context [ swi (?x < ?x != _) _] => is_evar x; unify x 0; try rewrite zerol
    end; rewrite ?eqxx /= /xor /=.

Ltac reduce_once :=
  simpl;
    match goal with
    | |- reduceI (@out _ _ _) _ _ => apply: reduce_outI
    | |- reduceI (@map _ _ _ _ _ _ _) _ _ => apply: reduce_mapI
    | |- reduceI (@sta _ _ _ _ _ _ _) _ _ => apply: reduce_staI
    | |- reduceI (@swi _ _ _ _) _ _ => apply: reduce_swiI
    | |- reduceI (par _ _) _ _ => apply: reduce_parI
    | |- reduceI (@loop _ _) _ _ => apply: reduce_loopI                                                  
    | |- reduceI (@maybe _ _ _) None _ => apply: reduce_maybeI
    | |- reduceI (@maybe _ _ _) (Some _) _ => apply: reduce_maybeI2

    | |- reduceO (@out _ _ _) _ _ => apply: reduce_outO
    | |- reduceO (@map _ _ _ _ _ _ _) _ _ => apply: reduce_mapO
    | |- reduceO (@sta _ _ _ _ _ _ _) _ _ => apply: reduce_staO
    | |- reduceO (@swi _ _ _ _) None _ => apply: reduce_swiO
    | |- reduceO (@swi _ _ _ _) (Some _) _ => apply: reduce_swiO2
    | |- reduceO (@swi _ _ false _) _ _ => apply: reduce_swiO
    | |- reduceO (@swi _ _ true _) _ _ => apply: reduce_swiO2                                                       
    | |- reduceO (par _ _) _ _ => apply: reduce_parO
    | |- reduceO (@loop _ _) _ _ => apply: reduce_loopO
    | |- reduceO (@maybe _ _ _) _ _ => apply: reduce_maybeO
    end.

Ltac debug_reduce :=
    match goal with
    | |- reduceI ?p ?i _ => idtac "reduceI" i
    | |- reduceO ?p ?o _ => idtac "reduceO" o
    end.

Ltac reduce_once_v :=
  simpl;
    match goal with
    | |- reduceI (@out _ _ _) _ _ => apply: reduce_outI
    | |- reduceI (@map _ _ _ _ _ _ _) ?i _ => idtac "map_in" i;apply: reduce_mapI
    | |- reduceI (@sta _ ?O _ _ _ ?v ?p) ?i _ => idtac "state" v;idtac "state input" i;idtac "continuation" p;idtac "output type" O;apply: reduce_staI
    | |- reduceI (@swi _ _ _ _) _ _ => apply: reduce_swiI
    | |- reduceI (par _ _) _ _ => apply: reduce_parI
    | |- reduceI (@loop _ _) _ _ => apply: reduce_loopI                                                  
    | |- reduceI (@maybe _ _ _) None _ => idtac "maybe none"; apply: reduce_maybeI
    | |- reduceI (@maybe _ _ _) (Some _) _ => idtac "maybe some"; apply: reduce_maybeI2

    | |- reduceO (@out _ _ _) _ _ => apply: reduce_outO
    | |- reduceO (@map _ _ _ _ _ _ _) ?o _ => idtac "map_out" o;apply: reduce_mapO
    | |- reduceO (@sta _ _ _ _ _ ?v _) _ _ => idtac "state" v;apply: reduce_staO
    | |- reduceO (@swi _ _ _ _) None _ => apply: reduce_swiO
    | |- reduceO (@swi _ _ _ _) (Some _) _ => apply: reduce_swiO2
    | |- reduceO (@swi _ _ false _) _ _ => apply: reduce_swiO
    | |- reduceO (@swi _ _ true _) _ _ => apply: reduce_swiO2                                                       
    | |- reduceO (par _ _) _ _ => apply: reduce_parO
    | |- reduceO (@loop _ _) _ _ => apply: reduce_loopO
    | |- reduceO (@maybe _ _ _) _ _ => apply: reduce_maybeO
    end.

Ltac controlled_eauto := 
    match goal with
    | |- reduceI _ _ _ => idtac
    | |- reduceO _ _ _ => idtac
    | |- _ => eauto                        
    end.

Ltac rewr := idtac. (*updated later*)
Ltac reduce_tac :=
  (try rewr);
   (repeat
      reduce_once);(try swi_instans);controlled_eauto; rewrite ?eqxx /= /xor /=.

Ltac reduce_tac_v :=
  (try rewr);(rewrite ?eqxx /= /xor /= );
   repeat first [reduce_once_v;first try econ | swi_instans].


Definition f_NI {I O :Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O]) (f : [I] -> [O]) := forall (l : level) (i i' : [I]), rel IRel l i i' -> rel ORel l (f i) (f i').
Definition f_PU {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O]) (f : [I] -> [O]) := forall l (i : [I]), dis IRel l i -> dis ORel l (f i).
Definition f_NI_PU {I O : Ty} (IRel : cEquiv [I]) (ORel : cEquiv [O]) (f : [I] -> [O])  := f_NI IRel ORel f /\ f_PU IRel ORel f.
Definition fv_NI (I O V: Ty) (IRel : cEquiv [I]) (ORel : cEquiv [O]) (VRel : cEquiv [V])  (f : [I] -> [V] -> [O]) := forall l (i i' : [I]), rel IRel l i i' -> forall (v v' : [V]), rel VRel l v v' -> rel ORel l (f i v) (f i' v').
Definition f_EP (I V: Ty) (IRel : cEquiv [I]) (VRel : cEquiv [V]) (f : [I] -> [V] -> [V]) := forall l i, dis IRel l i -> forall v, rel VRel l (f i v) v. (*equivalence preserving*)


 (*fixed typo in paper: In conclusion, replaced I with Bool * I  *)
Lemma rel_eqpair : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a b, rel (eqpair ARel BRel) l a b -> rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2.
Proof.
  ssa.
Qed.

Lemma rel_eqpair2 : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a b, 
    rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2 -> rel (eqpair ARel BRel) l a b.
Proof.
  ssa.
Qed.

Lemma rel_eqpair_R2 : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a1 a2 b1 b2,  rel ARel l a1 a2 /\ rel BRel l b1 b2 \/ dis BRel l b1 /\ dis BRel l b2 -> rel (eqpair_R ARel BRel) l (a1,b1) (a2,b2).
Proof.
  ssa.
Qed.

Lemma rel_eqpair_R2' : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a1 a2 b1 b2, rel (eqpair_R ARel BRel) l (a1,a2) (b1,b2) -> rel ARel l a1 b1 /\ rel BRel l a2 b2  \/ dis BRel l a2 /\ dis BRel l b2.
Proof.
  ssa.
Qed.

Lemma rel_eqpair_L2 : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a1 a2 b1 b2,  rel ARel l a1 a2 /\ rel BRel l b1 b2 \/ dis ARel l a1 /\ dis ARel l a2 -> rel (eqpair_L ARel BRel) l (a1,b1) (a2,b2).
Proof.
  ssa.
Qed.

Lemma rel_eqpair_L2' : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a1 a2 b1 b2, rel (eqpair_L ARel BRel) l (a1,b1) (a2,b2) -> rel ARel l a1 a2 /\ rel BRel l b1 b2  \/ dis ARel l a1 /\ dis ARel l a2.
Proof.
  ssa.
Qed.

Lemma rel_eqpair_LR : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a b, rel (eqpair_LR ARel BRel) l a b -> rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2.
Proof.
  intros. case: H; ssa; eauto.
Qed.

Lemma rel_eqpair_LR2 : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a1 a2 b1 b2,  rel ARel l a1 b1 /\ rel BRel l a2 b2 -> rel (eqpair_LR ARel BRel) l (a1,a2) (b1,b2).
Proof.
  intros. left. ssa.
Qed.

Lemma dis_eqpair_R : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a b, dis (eqpair_R ARel BRel) l (a,b) -> dis BRel l b.
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_R2 : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a b, dis BRel l b -> dis (eqpair_R ARel BRel) l (a,b).
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_L : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a b, dis (eqpair_L ARel BRel) l (a,b) -> dis ARel l a.
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_L2 : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a b, dis ARel l a -> dis (eqpair_L ARel BRel) l (a,b).
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_LR : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a b, dis (eqpair_LR ARel BRel) l (a,b) -> dis ARel l a /\ dis BRel l b.
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_LR2 : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l a b, dis ARel l a /\ dis BRel l b -> dis (eqpair_LR ARel BRel) l (a,b).
Proof.  
  intros. ssa.
  Qed.

Lemma f_NI_id (A : Ty) B : @f_NI A A B B id.
  rewrite /f_NI. done.
Qed.

Lemma f_PU_id (A : Ty) B : @f_PU A A B B id.
  rewrite /f_PU. done.
Qed.  
Hint Resolve (*f_NI_eq*) f_NI_id f_PU_id.

Ltac mrw := rewrite /f_NI /f_PU /fv_NI /f_EP.


Lemma f_NI_snd_eqpair : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]), f_NI (eqpair ARel BRel) BRel snd. 
Proof.
mrw. ssa.
Qed.

Lemma f_NI_snd_eqpair_LR : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]), f_NI (eqpair_LR ARel BRel) BRel snd. 
Proof.
mrw. intros. apply rel_eqpair_LR in H. ssa.
Qed.

Hint Resolve f_NI_snd_eqpair f_NI_snd_eqpair_LR: tempdb.


Lemma rel_eqsum : forall (A B : Ty) (a1 a2 : [A]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l, rel ARel l a1 a2 -> rel (eqsum ARel BRel) l (inl a1) (inl a2). 
Proof. ssa.
Qed.

Lemma rel_eqsum2 : forall (A B : Ty) (b1 b2 : [B]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l, rel BRel l b1 b2 -> rel (eqsum ARel BRel) l (inr b1) (inr b2). 
Proof. ssa.
Qed.

Lemma rel_eqsum' : forall (A B : Ty) (a1 a2 : [A]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l,rel (eqsum ARel BRel) l (inl a1) (inl a2) ->  rel ARel l a1 a2. 
Proof. ssa.
Qed.

Lemma rel_eqsum2' : forall (A B : Ty) (b1 b2 : [B]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l, rel (eqsum ARel BRel) l (inr b1) (inr b2) -> rel BRel l b1 b2. 
Proof. ssa.
Qed.

Lemma rel_eqsum_L : forall (A B : Ty) (a1 a2 : [A]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l, rel ARel l a1 a2 -> rel (eqsum_L ARel BRel) l (inl a1) (inl a2). 
Proof. ssa.
Qed.

Lemma rel_eqsum_L2 : forall (A B : Ty) (b1 b2 : [B]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l, rel BRel l b1 b2 -> rel (eqsum_L ARel BRel) l (inr b1) (inr b2). 
Proof. ssa.
Qed.

Lemma rel_eqsum_L' : forall (A B : Ty) (a1 a2 : [A]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l,rel (eqsum_L ARel BRel) l (inl a1) (inl a2) ->  rel ARel l a1 a2. 
Proof. ssa.
Qed.

Lemma rel_eqsum_L2' : forall (A B : Ty) (b1 b2 : [B]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l, rel (eqsum_L ARel BRel) l (inr b1) (inr b2) -> rel BRel l b1 b2. 
Proof. ssa.
Qed.

Lemma dis_eqsum_L : forall (A B : Ty) (a : [A]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l, dis ARel l a -> dis (eqsum_L ARel BRel) l (inl a). 
Proof. ssa.
Qed.

Lemma dis_eqsum_L2 : forall (A B : Ty) (a : [A]) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l, dis (eqsum_L ARel BRel) l (inl a) -> dis ARel l a. 
Proof. ssa.
Qed.


Lemma rel_eqpair_to_L : forall (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l x y, rel (eqpair ARel BRel) l x y -> rel (eqpair_L ARel BRel) l x y.
Proof.
  ssa.
Qed.

Lemma simp_pair1 : forall (A B: Type) (a : A) (b : B), (a,b).1 = a.
Proof. done.
Qed.
Lemma simp_pair2 : forall (A B: Type) (a : A) (b : B), (a,b).2 = b.
Proof. done.
Qed.

Definition pair_rewr := (simp_pair1,simp_pair2).

Lemma rel_eqmaybe_all : forall (A : Ty) (ARel : cEquiv [A]) l x y, rel ARel l x y -> rel (eqmaybe_all ARel) l (Some x) (Some y).
Proof. ssa.
Qed.


Lemma level_not : forall (l : level), ~ (l <> \bot) -> l = \bot.
  intros. de (eqVneq l \bot). exfalso. apply H. intro. subst. by rewrite eqxx in i.
Qed.
Hint Resolve level_not.


Ltac inner_match H := match H with
                      | context[match ?x with _ => _ end] => first [ inner_match x | idtac x;de x ]
                      end.                                             

Ltac temp_tac := (match reverse goal with
                  | H : _ \/ _ |- _ => de H
                  | H : match ?x with _ => _ end |- _ => de x
                  | |- ?H => inner_match H
                  end                      
                  ;subst;ssa).

Lemma rel_eqmaybe_nonbot_aux : forall (A : Ty) (ARel : cEquiv [A]) l x y, rel (eqmaybe_nonbot ARel) l x y -> match x,y with
                                                                                                      | Some x', Some y' => rel ARel l x' y'
                                                                                                      | Some x', None => l = \bot /\ dis ARel l x'
                                                                                                      | None, Some y' => l = \bot /\ dis ARel l y'
                                                                                                      | None, None => True
                                                                                                      end.
Proof.
  intros.
  temp_tac.
  temp_tac.
  temp_tac.
Qed.

Lemma rel_eqmaybe_nonbot : forall (A : Ty) (ARel : cEquiv [A]) l x y, rel (eqmaybe_nonbot ARel) l x y -> (exists x' y', x = Some x' /\ y = Some y' /\ rel ARel l x' y') \/
                                                                                                    (exists x', x = Some x' /\ y = None /\ l = \bot /\ dis ARel l x') \/
                                                                                                    (exists y', x = None /\ y = Some y' /\ l = \bot /\ dis ARel l y') \/ x = None /\ y = None.
Proof.
  intros. de x. de y. left. eauto.
  right. left. econ.  eauto.
  de y. right. right. econ. econ. eauto.
Qed.

Lemma rel_eqmaybe_nonbot2 : forall (A : Ty) (ARel : cEquiv [A]) l x y, rel ARel l x y -> rel (eqmaybe_nonbot ARel) l (Some x) (Some y).
Proof. ssa.
Qed.

Lemma rel_eqmaybe_nobody2 : forall (A : Ty) (ARel : cEquiv [A]) l x y, rel ARel l x y -> rel (eqmaybe_nobody ARel) l (Some x) (Some y).
Proof. ssa.
Qed.


Lemma rel_eqmaybe_all_aux : forall (A : Ty) (ARel : cEquiv [A]) l x y, rel (eqmaybe_all ARel) l x y -> match x,y with
                                                                                              | Some x', Some y' => rel ARel l x' y'
                                                                                              | Some x', None => dis ARel l x'
                                                                                              | None, Some y' => dis ARel l y'
                                                                                              | None, None => True
                                                                                              end.
Proof.
  intros.
  temp_tac.
  temp_tac.
  temp_tac.
Qed.

Lemma rel_eqmaybe_all2 : forall (A : Ty) (ARel : cEquiv [A]) l x y, rel (eqmaybe_all ARel) l x y -> (exists x' y', x = Some x' /\ y = Some y' /\ rel ARel l x' y') \/
                                                                                             x = None /\ y = None.
Proof.
  intros.
  de x. de y.
  left. eauto.
  de y.
Qed.

Lemma rel_eqmaybe_aware2 : forall (A : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [Bool]) l x y, rel (eqmaybe_aware ARel BRel) l x y -> (exists x' y', x = Some x' /\ y = Some y' /\ rel ARel l x' y') \/
                                                                                                                                (x = None /\ y = None) \/ (eqmaybe_dis (aware BRel true) ARel l x /\ eqmaybe_dis (aware BRel true) ARel l y).
Proof.
  intros.
  de x. de y.
  left. eauto.
  de y.
Qed.

Lemma dis_eqmaybe_all : forall (A : Ty) (ARel : cEquiv [A]) l v, dis (eqmaybe_all ARel) l v -> exists v', v = Some v' /\ dis ARel l v'.
Proof.
  intros. ssa. de v. econ. eauto.
Qed.

Lemma dis_eqmaybe_all2 : forall (A : Ty) (ARel : cEquiv [A]) l x, dis ARel l x -> dis (eqmaybe_all ARel) l (Some x). 
Proof.
  intros. ssa. 
Qed.

Lemma dis_eqmaybe_nobody2 : forall (A : Ty) (ARel : cEquiv [A]) l x, dis ARel l x -> dis (eqmaybe_nobody ARel) l (Some x). 
Proof.
  intros. ssa. 
Qed.    

Definition is_inl (A B : Set) (x : A + B) := if x is inl _ then true else false.
Definition is_inr (A B : Set) (x : A + B) := if x is inr _ then true else false.


Lemma aware_public : aware (public_equiv Bool) true \bot.
Proof. rewrite /aware. ssa.
Qed.
Hint Resolve aware_public.
