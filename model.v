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

Parameter (level : tbLatticeType (Order.Disp tt tt)).

(*Definition unit_indDef := [indDef for option_rect].
Canonical unit_indType := IndType unit unit_indDef.
Definition unit_hasDecEq := [derive hasDecEq for unit].
HB.instance Definition _ := unit_hasDecEq.*)

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
    end; auto.


Ltac ssa' := rewrite ?inE;simpl in *; split_and;try done.
Ltac ssa := rewrite ?inE;simpl in *; split_ando;try done.

Ltac de i := destruct i;ssa.

Ltac case_if := match goal with 
                | [ |- context[if ?X then _ else _ ]] => have : X by subst
                | [ |- context[if ?X then _ else _ ]] => have : X = false by subst 

                | [ |- context[if ?X then _ else _ ]] => let H := fresh in destruct X eqn:H

                end; try (move=>->).

Lemma coseq_match : forall {A : Type} (g : Stream A), g = match g with | Cons a b => Cons a b end.  
Proof. move => A[] //=. Qed. 

Ltac coseq_tac l := rewrite (coseq_match l) /=. 
Ltac coseq_tac_in l H := rewrite (coseq_match l) /= in H.

Definition order (b1 b2 : level) := b1 <= b2.

Record myrel (A : Set) :=
        MyRel {
           dis : level -> A -> Prop;
           rel : level -> A -> A -> Prop;
           equiv : forall l, Equivalence (rel l);
           _ : forall l0 l1, order l0 l1 ->
                             forall a0 a1, rel l1 a0 a1 -> rel l0 a0 a1;
           _ : forall l0 l1, order l0 l1 ->
                             forall a, dis l1 a -> dis l0 a;
           _: forall l a0, dis l a0 -> forall a1, dis l a1 <-> rel l a0 a1 (* dis is an equivalence class: (->) contains enough, (<-) does not include too much s  *)
(*           _: forall l a0 a1, dis l a0 -> rel l a0 a1 -> dis l a1;
           _: forall l a0 a1, dis l a0 -> dis l a1 -> rel l a0 a1*)
          }.

(*Existing Class myrel. 
Hint Mode myrel +.*)

(* Types *)

(*Example 3*)
Inductive Interrupt := DiskInterrupt.
Inductive HandlerOutput := Nothing | Notify.
Inductive TypeSyscall := Syscall | NOP.
Inductive PublicOutput := GetRequest | Public_NOP.
Inductive PublicInput := PublicIn
.
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

Definition PublicInput_indDef := [indDef for PublicInput_rect].
Canonical PublicInput_indType := IndType PublicInput PublicInput_indDef.
Definition PublicInput_hasDecEq := [derive hasDecEq for PublicInput].
HB.instance Definition _ := PublicInput_hasDecEq.

Inductive Input := Skip | DiskRead.
Inductive Output := Idle | Step.


Definition Input_indDef := [indDef for Input_rect].
Canonical Input_indType := IndType Input Input_indDef.
Definition Input_hasDecEq := [derive hasDecEq for Input].
HB.instance Definition _ := Input_hasDecEq.

Definition Output_indDef := [indDef for Output_rect].
Canonical Output_indType := IndType Output Output_indDef.
Definition Output_hasDecEq := [derive hasDecEq for Output].
HB.instance Definition _ := Output_hasDecEq.

Inductive Ty : Set := Nat | Times : Ty -> Ty -> Ty | Bool
                 | Option : Ty -> Ty | Sum : Ty -> Ty -> Ty | TInput | TOutput | TTypeSyscall | Unit | TInterrupt | THandlerOutput |  TPublicOutput | TPublicInput. 

Derive NoConfusion for Ty.
Derive EqDec for Ty.

Definition Ty_indDef := [indDef for Ty_rect].
Canonical Ty_indType := IndType Ty Ty_indDef.
Definition Ty_hasDecEq := [derive hasDecEq for Ty].
HB.instance Definition _ := Ty_hasDecEq.

Fixpoint interp (t : Ty) : Set :=
  match t with
  | Nat => nat
  | Times t0 t1 => (interp t0) * (interp t1)
  | Bool => bool
  | Option t' => option (interp t')
  | TInput => Input
  | TOutput => Output
  | Sum t0 t1 => (interp t0) + (interp t1)            
  | TTypeSyscall => TypeSyscall
  | Unit => unit                     
  | TInterrupt => Interrupt
  | THandlerOutput => HandlerOutput
  | TPublicOutput => PublicOutput
  | TPublicInput => PublicInput                       
  end.
Notation "[ i ]" := (interp i).



(** Process type **)
Inductive Proc : Ty -> Ty -> Type :=
| out  : forall {I O : Ty}, interp O -> Proc I O  
| map   : forall {I I' O O' : Ty}, (interp I -> interp I') -> (interp O -> interp O') -> Proc I' O -> Proc I O'
| sta   : forall {I O V :Ty}, (interp I -> interp V -> interp V) -> (interp O -> interp V -> interp V) -> interp V -> Proc (Times V I) O -> Proc I (Times V O)
| swi   : forall {I O : Ty},  bool -> Proc I (Times Bool O)%type -> Proc ((Times Bool I)) (Option O)
| par   : forall {I O1 O2: Ty}, Proc I O1 -> Proc I O2 -> Proc I (Times O1 O2)
| loop  : forall {I : Ty}, Proc I I -> Proc I I
| maybe : forall {I O: Ty}, Proc I O -> Proc (Option I) O.
Arguments out {_} {_} o.
Derive NoConfusion for Proc.
Derive NoConfusionHom for Proc.
Derive Signature for Proc.

Definition xor (b1 b2 : bool) := (Datatypes.negb (b1 == b2)).

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

(*Create HintDb omitdb.
Hint Resolve reduce_mapI reduce_staI reduce_swiI reduce_maybeI reduce_maybeI2 reduce_parI reduce_loopI : omitdb.*)

Inductive reduceO : forall (I O : Ty), Proc I O -> [O] -> Proc I O -> Prop :=
| reduce_outO (I O : Ty) (o : [O]) : reduceO ( @out I _ o) o ( @out I _ o)
| reduce_mapO (I I' O O' : Ty) p p' o o' (f : [I] -> [I']) (g : [O] -> [O']) : g o = o' -> reduceO p o p' -> reduceO (map f g p) o' (map f g p')
| reduce_staO (V I O : Ty) v v' p p' o (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) : g o v = v' -> reduceO p o p' -> reduceO (sta f g v p) (v', o) (sta f g v' p')
| reduce_swiO (I O : Ty) (p : Proc I (Times Bool O)): reduceO (swi false p) None (swi false p)
| reduce_swiO2 (I O : Ty) b b' (p : Proc I (Times Bool O)) p' (o : [O]) : b' = xor true b -> reduceO p (b, o) p' -> reduceO (swi true p) (Some o) (swi b' p')
| reduce_maybeO (I O : Ty) (p p' : Proc I O) (o : [O]) : reduceO p o p' -> reduceO (maybe p) o (maybe p')
| reduce_parO (I O1 O2 : Ty) (p1 p1' : Proc I O1) (p2 p2' : Proc I O2) (o : [O1]) (o' : [O2]) : reduceO p1 o p1' -> reduceO p2 o' p2' -> reduceO (par p1 p2) (o, o') (par p1' p2')
| reduce_loopO (O :Ty) (p p' p'' : Proc O O) (o : [O]) : reduceO p o p' -> reduceI p' o p'' -> reduceO (loop p) o (loop p'').
Hint Constructors reduceO : core.

Ltac check_if_var x :=
  first [ is_var x;fail 1 "Term" x "is not a bare variable" | idtac ].

Ltac match_dd_once := 
    match goal with
    | H : reduceI ?p _ _ |- _ => check_if_var p; dependent destruction  H
    | H : reduceO ?p _ _ |- _ => check_if_var p; dependent destruction  H
    end.


Ltac match_dd := 
   repeat match_dd_once.

Ltac match_dd_o := 
   repeat (match_dd_once;eauto).
(*Hint Resolve reduce_mapO reduce_staO reduce_swiO reduce_swiO2 reduce_maybeO reduce_parO reduce_loopO : omitdb.*)


Variant TraceF {I O : Ty} (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O -> Prop :=
  | traceI : forall p p' i effs, reduceI p i p' -> R effs p'  -> TraceF R (Cons (inl i) effs) p
  | traceO : forall p p' o effs, reduceO p o p' -> R effs p'  -> TraceF R (Cons (inr o) effs) p.
Hint Constructors TraceF.

Lemma monotone_TraceF {I O : Ty} : monotone2 (@TraceF I O).
Proof.
intro.  ssa.
inv IN; eauto.
Qed.
Hint Resolve monotone_TraceF : paco.

Definition trace (I O : Ty) eff p := paco2 (@TraceF I O) bot2 eff p.

Variant MapSF (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (R : Stream ([I'] + [O]) -> Stream ([I] + [O']) -> Prop) : Stream ([I'] + [O]) -> Stream ([I] + [O']) -> Prop :=
  | MapI i i' s s' : R s' s -> f i = i' -> MapSF f g R (Cons (inl i') s') (Cons (inl i) s)
  | MapO o o' s s' : R s' s -> g o = o' -> MapSF f g R (Cons (inr o) s') (Cons (inr o') s).

Lemma MapSF_monotone2 : forall (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']), monotone2 (@MapSF I I' O O' f g).
Proof.
Admitted.
Hint Resolve MapSF_monotone2 : paco.

Definition MapS  (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) s s' := paco2 (@MapSF I I' O O' f g) bot2 s s'.

Definition MapRel (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) s p := exists s', MapS f g s' s /\ trace s' p.



(*Lemma MapSP : forall (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) s p, trace s (map f g p) -> exists s', MapS f g s' s /\ trace s' p.
Proof.*)

Definition boolRel : myrel ([Bool]).
  refine (@MyRel _
            (fun l (b : [Bool]) => b \/ l = \bot)
            (fun l b1 b2 => b1 = b2 \/  (b1 \/ l = \bot) /\ (b2 \/ l = \bot))
            _
            _
            _
            _).
intros.
con. intro. intros. auto. intro. intros. de H. intro. intros. de H. subst. de H0. de H0. subst. de H.
intros. de H0. de H0. de H1. subst.
rewrite /order in H.
rewrite lex0 in H. rewrite (eqP H). de a0.
subst.
rewrite /order in H.
rewrite lex0 in H. rewrite (eqP H). de a0.
intros. de H0. subst.
rewrite /order in H.
rewrite lex0 in H. right. apply/eqP. done.
intros. con. intros. de H. de H.
de H0. de a0.
Defined.

Definition falseRel : myrel ([Bool]).
  refine (@MyRel _
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

Definition publicRel (A : Ty) : myrel ([A]).
  refine (@MyRel _
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

Definition toPublicRel (A : Ty) (ARel : myrel [A]) : myrel ([A]).
  refine (@MyRel _
            (fun l b => False)
            (rel ARel)
            _
            _
            _
            _).
intros. all: de ARel. eauto.
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

Definition privateRel (A : Ty) : myrel ([A]).
  refine (@MyRel _
            (fun l b => True)
            (fun l b1 b2 => True) (*Since everything is always hidden, there the value space is an equivalence class*)
            _
            _
            _
            _).
intros.
done. done.
intros. done. done.
Defined.

  
Definition semiprivateRel (A : Ty) : myrel ([A]).
  refine (@MyRel _
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


Definition Clause1 (I O : Ty) (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  forall i s', s = (Cons (inl i) s') -> dis IRel l i -> R s' p.

Definition Clause2 (I O : Ty) (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  (forall i, dis IRel l i -> exists p', reduceI p i p' /\ R s p').

Definition Clause3 (I O : Ty) (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  forall i s', s = (Cons (inl i) s') -> (forall i', rel IRel l i' i -> exists p', reduceI p i' p' /\ R s' p').

Definition Clause4 (I O : Ty) (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  forall o s', s = (Cons (inr o) s') -> exists o', rel ORel l o' o /\ exists p', reduceO p o' p' /\ R s' p'.

Variant SimulationF (I O : Ty) (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | SI s p  : Clause1 l IRel ORel R s p ->
              Clause2 l IRel ORel R s p ->
              Clause3 l IRel ORel R s p ->
              Clause4 l IRel ORel R s p ->
              SimulationF l IRel ORel R s p.

Ltac rc := rewrite /Clause1 /Clause2 /Clause3 /Clause4.
Lemma monotone_Clause1 {I O : Ty}  l IRel ORel :  monotone2 (@Clause1 I O l  IRel ORel ).
Proof.
intro. ssa. rc. eauto.
Qed.

Lemma monotone_Clause2 {I O : Ty}  l  IRel ORel  :  monotone2 (@Clause2 I O l  IRel ORel ).
Proof.
  intro. rc. ssa. 
  move: (IN _ H). ssa. eauto.
Qed.

Lemma monotone_Clause3 {I O : Ty}  l  IRel ORel  :  monotone2 (@Clause3 I O l  IRel ORel ).
Proof.
  intro. rc. ssa. subst.
  move: (IN _ _ Logic.eq_refl _ H0). ssa. eauto.
Qed.

Lemma monotone_Clause4 {I O : Ty}  l  IRel ORel  :  monotone2 (@Clause4 I O l  IRel ORel ).
Proof.
  intro. rc. ssa. subst.
  move: (IN _ _ Logic.eq_refl). ssa. eauto.
  exists x. ssa. eauto.
Qed.


Lemma monotone_SimulationF {I O : Ty} IRel ORel l:  monotone2 (@SimulationF I O l IRel ORel).
Proof.
rewrite /monotone2. ssa.
inv IN.
eapply SI.
eapply monotone_Clause1. eauto. eauto.
eapply monotone_Clause2. eauto. eauto.
eapply monotone_Clause3. eauto. eauto.
eapply monotone_Clause4. eauto. eauto.
Qed.
Hint Resolve monotone_SimulationF : paco.

Definition simulation {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) l s p := paco2 (@SimulationF I O l IRel ORel) bot2 s p.
Definition NI (I O :Ty) (IRel : myrel [I]) (ORel : myrel [O])  (p : Proc I O) := forall l s, trace s p -> simulation IRel ORel l s p.

Check paco2.

Lemma paco2_imp : forall A B (a : A) (b : B) F F' R, monotone2 F -> (forall a b R, F R a b -> F' R a b) -> paco2 F R a b -> paco2 F' R a b.
Proof.
  intros. move: a b H1. pcofix CIH. intros. pfold. apply H0.
  punfold H2. eapply H. apply:H2.
  intros. inv PR. right. apply CIH. done. right. eauto.
Qed.

Lemma paco2_iff : forall A B (a : A) (b : B) F F' R, monotone2 F -> monotone2 F' -> (forall a b R, F R a b <-> F' R a b) -> paco2 F R a b <-> paco2 F' R a b.
Proof.
  intros. split;apply/paco2_imp;eauto.
  intros. apply/H1. eauto.
  intros. apply/H1. eauto.
Qed.  

Lemma SimulationF_imp : forall I O l (IRel : myrel [I]) (ORel : myrel [O]) R s p, SimulationF l IRel ORel R s p -> SimulationF l IRel (toPublicRel ORel) R s p.
Proof.
  intros. inv H. con;eauto.
Qed.

Lemma SimulationF_imp2 : forall I O l (IRel : myrel [I]) (ORel : myrel [O]) R s p, SimulationF l IRel (toPublicRel ORel) R s p -> SimulationF l IRel ORel R s p.
Proof.
  intros. inv H. con;eauto.
Qed.



Lemma simulation_equiv : forall I O (IRel : myrel [I]) (ORel : myrel [O]) p, NI IRel ORel p <-> NI IRel (toPublicRel ORel) p.
Proof.
  intros. split.
  intros. rewrite /NI. intros. eapply H in H0.
  move: H0. instantiate (1:=l).
  apply:paco2_imp. apply monotone_SimulationF.
  intros. apply/SimulationF_imp. done.

  intros. rewrite /NI. intros. eapply H in H0.
  move: H0. instantiate (1:=l).
  apply:paco2_imp. apply monotone_SimulationF.
  intros. apply/SimulationF_imp2. eauto.
Qed.  


Definition eqpair {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Times I O]).
  refine (@MyRel _ 
            (fun (l : level) _ => False)
            (fun l io1 io2 => rel IRel l (fst io1) (fst io2) /\ rel ORel l (snd io1) (snd io2))
            _
            _
            _
            _).
  - move=> l. 
    con. destruct IRel. destruct ORel. simpl. con.
    move: (equiv0 l). case. eauto.
    move: (equiv1 l). case. eauto.
  - con. destruct H. destruct IRel. destruct ORel. simpl. 
    move: (equiv0 l). case.
    move => _ Hsym _.  apply Hsym. eauto.

    destruct H. destruct IRel. destruct ORel. simpl. 
    move: (equiv1 l). case. eauto.

  - destruct IRel,ORel. simpl. con.
    ssa. move: (equiv0 l). case. move=> _ _ Htrans. eauto.
    ssa. move: (equiv1 l). case. move=> _ _ Htrans. eauto.


  - move=> l0 l1 HOrder a0 a1 [] HI HO.
    destruct IRel,ORel;ssa. eauto. eauto.

  - eauto.

    intros. con.
done.
done.
Defined.

Definition eqpair_LR {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Times I O]).
  refine (@MyRel _ 
            (fun (l : level) io => dis IRel l (fst io) /\ dis ORel l (snd io))
            (fun l io1 io2 => rel IRel l (fst io1) (fst io2) /\ rel ORel l (snd io1) (snd io2))
            _
            _
            _
            _).
  - move=> l. 
    con. destruct IRel. destruct ORel. simpl. con.
    move: (equiv0 l). case. eauto.
    move: (equiv1 l). case. eauto.
  - con. destruct H. destruct IRel. destruct ORel. simpl. 
    move: (equiv0 l). case.
    move => _ Hsym _.  apply Hsym. eauto.

    destruct H. destruct IRel. destruct ORel. simpl. 
    move: (equiv1 l). case. eauto.

  - destruct IRel,ORel. simpl. con.
    ssa. move: (equiv0 l). case. move=> _ _ Htrans. eauto.
    ssa. move: (equiv1 l). case. move=> _ _ Htrans. eauto.


  - move=> l0 l1 HOrder a0 a1 [] HI HO.
    destruct IRel,ORel;ssa. eauto. eauto.

  - intros. ssa. de IRel. eauto. de ORel. eauto.
  - intros. ssa. de IRel. con.
    ssa. apply/i;eauto.
    de ORel. apply/i0;eauto.
    ssa. apply/i;eauto.
    de ORel. apply/i0;eauto.
Defined.

Definition eqpair_L {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Times I O]).
  refine (@MyRel _ 
            (fun (l : level) io => dis IRel l (fst io))
            (fun l io1 io2 => rel IRel l (fst io1) (fst io2) /\ rel ORel l (snd io1) (snd io2) \/ dis IRel l (fst io1) /\ dis IRel l (fst io2))
            _
            _
            _
            _).
  - move=> l. 
    con. destruct IRel. destruct ORel. simpl. con.
    move: (equiv0 l). case. eauto.
    move: (equiv1 l). case. eauto.
  - rewrite /Symmetric. intros. destruct H. destruct IRel. destruct ORel. simpl.
    ssa. left.
    move: (equiv0 l). case.
    move => _ Hsym _. con.  apply Hsym. eauto.

    move: (equiv1 l). case.
    move => _ Hsym' _.  apply Hsym'. eauto.

    ssa.

  - destruct IRel,ORel. simpl. intro. intros.

    de H. de H0. left. ssa.
    move: (equiv0 l). case. move=> _ _ Htrans. eauto.
    move: (equiv1 l). case. move=> _ _ Htrans. eauto.

    right. ssa. apply/i. apply: H0.
    move: (equiv0 l). case.
    move=> _ Hsym _. apply/Hsym. done.

    de H0.

    right. ssa. apply/i. apply: H1. done.


  - intros. de H0.
    left.
    de IRel;eauto.
    de ORel;eauto.
    right.
    de IRel;eauto.

  - intros. de IRel;eauto.

  - intros. con.
    intros. eauto.
    case. case. move=> HH _.
    de IRel;eauto. apply/i. 2:eauto. done.
    ssa.
Defined.

Definition eqpair_R {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Times I O]).
  refine (@MyRel _ 
            (fun (l : level) io => dis ORel l (snd io))
            (fun l io1 io2 => rel IRel l (fst io1) (fst io2) /\ rel ORel l (snd io1) (snd io2) \/ dis ORel l (snd io1) /\ dis ORel l (snd io2))
            _
            _
            _
            _).
  - move=> l. 
    con. destruct IRel. destruct ORel. simpl. con.
    move: (equiv0 l). case. eauto.
    move: (equiv1 l). case. eauto.
  - rewrite /Symmetric. intros. destruct H. destruct IRel. destruct ORel. simpl.
    ssa. left.
    move: (equiv0 l). case.
    move => _ Hsym _. con.  apply Hsym. eauto.

    move: (equiv1 l). case.
    move => _ Hsym' _.  apply Hsym'. eauto.

    ssa.

  - destruct IRel,ORel. simpl. intro. intros.

    de H. de H0. left. ssa.
    move: (equiv0 l). case. move=> _ _ Htrans. eauto.
    move: (equiv1 l). case. move=> _ _ Htrans. eauto.

    right. ssa. apply/i0. apply: H0.
    move: (equiv1 l). case.
    move=> _ Hsym _. apply/Hsym. done.

    de H0.

    right. ssa. apply/i0. apply: H1. done.


  - intros. de H0.
    left.
    de IRel;eauto.
    de ORel;eauto.
    right.
    de IRel;eauto.

  - intros. de ORel;eauto. de ORel;eauto.

  - intros. de ORel;eauto.
    intros. con. ssa.
    case. case. intros. de ORel. apply/i. 2:eauto. done.
    case. ssa.
Defined.

Lemma dis_rel_dis : forall (I : Ty) (IRel : myrel [I]) l x y, dis IRel l x -> rel IRel l x y -> dis IRel l y.
Proof.
  intros. de IRel. apply/i;eauto.
Qed.
Lemma dis_rel_dis2 : forall (I : Ty) (IRel : myrel [I]) l x y, dis IRel l x -> rel IRel l y x -> dis IRel l y.
Proof.
  intros. de IRel. apply/i;eauto.
  move:(equiv0 l)=> [] _ Hsym _. apply/Hsym. auto.
Qed.
Lemma dis_dis_rel : forall (I : Ty) (IRel : myrel [I]) l x y, dis IRel l x -> dis IRel l y -> rel IRel l x y.
Proof.
  intros. de IRel;eauto. apply/i;eauto.
Qed.


Hint Resolve dis_rel_dis dis_rel_dis2 dis_dis_rel.



Definition eqpair_OR {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Times I O]).
  refine (@MyRel _ 
            (fun (l : level) io => dis IRel l (fst io) \/ dis ORel l (snd io))
            (fun l io1 io2 => rel IRel l (fst io1) (fst io2) /\ rel ORel l (snd io1) (snd io2) \/
                                (dis IRel l (fst io1) \/ dis ORel l (snd io1)) /\
                                (dis IRel l (fst io2) \/ dis ORel l (snd io2))                                  
            )
            _
            _
            _
            _).
  - move=> l. 
    con. destruct IRel. destruct ORel. simpl. con.
    move: (equiv0 l). case. eauto.
    move: (equiv1 l). case. eauto.
  - intro. intros. destruct H.
    left. destruct IRel,ORel. simpl in *.
    destruct H.
    con.
    move: (equiv0 l)=> [] _ Hsym _.
    apply/Hsym. done.
    move: (equiv1 l)=> [] _ Hsym _.
    apply/Hsym. done. ssa.

    
    intro. intros.
    de H.
    * de H0.
      ** left. con.
         de IRel. move: (equiv0 l)=>[] _ _ Htrans. apply/Htrans;eauto.
         de ORel. move: (equiv0 l)=>[] _ _ Htrans. apply/Htrans;eauto.    
      ** de H0. have: dis IRel l x.1 by eauto. move=>HH.
         right. con. auto. auto.
         have: dis ORel l x.2 by eauto. move=>HH.
         right. con. auto. auto.
    * de H0. right. con. auto.
      de H1. eauto. eauto.


      intros. destruct H0.
      ** left. destruct IRel. destruct ORel. simpl in *. ssa;eauto.
      ** right. destruct IRel. destruct ORel. simpl in *. ssa;eauto.
         de H0;eauto. de H1;eauto.


         intros. destruct IRel. destruct ORel. simpl in *.
         destruct H0;eauto.


         intros. con. intros. de H.
         case. case. intros. de H. eauto. eauto.
         de H.
Defined.

Lemma eqsum_LR {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Sum I O]).
  refine (@MyRel _ 
            (fun (l : level) io => match io with | inl i => dis IRel l i | inr o => dis ORel l o end)
            (fun l io1 io2 => match io1,io2 with | inl i1,inl i2 => rel IRel l i1 i2
                                            | inr o1,inr o2 => rel ORel l o1 o2
                                            | inl i1, inr i2 => dis IRel l i1 /\ dis ORel l i2
                                            | inr i1, inl i2 => dis ORel l i1 /\ dis IRel l i2 end)
            _
            _
            _
            _).
  - move=> l. 
    con.
    intro. 
    destruct IRel. destruct ORel. simpl. de x.
    move: (equiv0 l). case. eauto.
    move: (equiv1 l). case. eauto.

    destruct IRel. destruct ORel. simpl.
    intro. ssa. de x. de y.
    move: (equiv0 l). case. eauto. 
    move: (equiv1 l). case. de y.

    destruct IRel. destruct ORel. simpl.
    intro. ssa. de x. de y. de z.
    move: (equiv0 l). case. eauto. apply/i. 2:eauto.
    move: (equiv1 l). case. eauto.

    move: (equiv0 l). case. eauto. 
    de z. apply/i. done. done.
    apply/i0. eauto.
    done.
    de y. de z. apply/i. 2:eauto. done.
    apply/i0. done. done.
    de z. apply/i0. eauto.
    move:(equiv1 l)=> [] _ Hsym _. eauto.
    move:(equiv1 l)=> [] _ _ Htrans. eauto.


    intros. de a0. de a1. de IRel;eauto. de IRel;eauto.
    de ORel;eauto.
    de a1. de ORel;eauto. de IRel;eauto. de ORel;eauto.


    intros. de a. de IRel;eauto. de ORel;eauto.

    intros. con.
    intros. de a0. de a1. de a1.
    de a0. de a1. eauto.
    de a1. eauto.
Defined.

Lemma eqsum_L {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Sum I O]).
  refine (@MyRel _ 
            (fun (l : level) io => match io with | inl i => dis IRel l i | inr _ => False  end)
            (fun l io1 io2 => match io1,io2 with | inl i1,inl i2 => rel IRel l i1 i2
                                            | inr o1,inr o2 => rel ORel l o1 o2
                                            | _,_ => False end)
            _
            _
            _
            _).
  - move=> l. 
    con.
    intro. 
    destruct IRel. destruct ORel. simpl. de x.
    move: (equiv0 l). case. eauto.
    move: (equiv1 l). case. eauto.

    destruct IRel. destruct ORel. simpl.
    intro. ssa. de x. de y.
    move: (equiv0 l). case. eauto. 
    move: (equiv1 l). case. de y.

    destruct IRel. destruct ORel. simpl.
    intro. ssa. de x. de y. de z.
    move: (equiv0 l). case. eauto. de y. de z. 
    move: (equiv1 l). case. move=> _ _ Htrans. apply/Htrans. eauto. done.
    intros. de a0. de a1. de IRel;eauto. de IRel;eauto.
    de ORel;eauto.
    de a1. eauto.
    
    intros. de a. de IRel;eauto.
    
    intros. con.
    intros. de a0. de a1. de a0.
    de a1. 
    de IRel. apply/i1;eauto.
Defined.

Lemma eqsum_R {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Sum I O]).
  refine (@MyRel _ 
            (fun (l : level) io => match io with | inl _ => False | inr o => dis ORel l o end)
            (fun l io1 io2 => match io1,io2 with | inl i1,inl i2 => rel IRel l i1 i2
                                            | inr o1,inr o2 => rel ORel l o1 o2
                                            | _,_ => False end)
            _
            _
            _
            _).
  - move=> l. 
    con.
    intro. 
    destruct IRel. destruct ORel. simpl. de x.
    move: (equiv0 l). case. eauto.
    move: (equiv1 l). case. eauto.

    destruct IRel. destruct ORel. simpl.
    intro. ssa. de x. de y.
    move: (equiv0 l). case. eauto. 
    move: (equiv1 l). case. de y.

    destruct IRel. destruct ORel. simpl.
    intro. ssa. de x. de y. de z.
    move: (equiv0 l). case. eauto. de y. de z. 
    move: (equiv1 l). case. move=> _ _ Htrans. apply/Htrans. eauto. done.
    intros. de a0. de a1. de IRel;eauto. de IRel;eauto.
    de ORel;eauto.
    de a1. eauto.
    
    intros. de a. de IRel;eauto. de ORel;eauto.
    
    intros. con.
    intros. de a0. de a1. de a0.
    de a1. 
    de IRel. de ORel. apply/i2;eauto.
Defined.



Lemma eqsum {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Sum I O]).
  refine (@MyRel _ 
            (fun (l : level) io => False)
            (fun l io1 io2 => match io1,io2 with | inl i1,inl i2 => rel IRel l i1 i2
                                            | inr o1,inr o2 => rel ORel l o1 o2
                                            | _,_ => False
                                            end)           
            _
            _
            _
            _).
  - move=> l. 
    con.
    intro. 
    destruct IRel. destruct ORel. simpl. de x.
    move: (equiv0 l). case. eauto.
    move: (equiv1 l). case. eauto.

    destruct IRel. destruct ORel. simpl.
    intro. ssa. de x. de y.
    move: (equiv0 l). case. eauto. 
    move: (equiv1 l). case. de y.

    destruct IRel. destruct ORel. simpl.
    intro. ssa. de x. de y. de z.
    move: (equiv0 l). case. eauto.
(*    apply/i. 2:eauto.
    move: (equiv1 l). case. eauto.

    move: (equiv0 l). case. eauto. *)
    de z. de y. de y.
    move: (equiv1 l). case. move=> _ _ Htrans. apply/Htrans. eauto. eauto.

    
(*    apply/i. done. done.
    apply/i0. eauto.
    done.
    de y. de z. apply/i. 2:eauto. done.
    apply/i0. done. done.
    de z. apply/i0. eauto.
    move:(equiv1 l)=> [] _ Hsym _. eauto.
    move:(equiv1 l)=> [] _ _ Htrans. eauto.*)


    intros. de a0. de a1. de IRel;eauto. de IRel;eauto.
    de ORel;eauto.
    de a1. eauto.
    done.

(*    intros. de a. de IRel;eauto. de ORel;eauto.*)

    intros. con. done.
(*    intros. de a0. de a1. de a1.*)
    de a0.
(*    de a1. eauto.
    de a1. eauto.*)
Defined.

Definition levelPred := level -> Prop.
Definition presP (P:levelPred) := forall x0 x1, order x0 x1 -> P x0 -> P x1.

Lemma rel_refl : forall (A : Ty) (ARel : myrel [A]) l x, rel ARel l x x.
Proof.
  intros. de ARel. move:(equiv0 l). case. eauto.
Qed.
Lemma rel_sym : forall A (ARel : myrel A) l x y, rel ARel l x y -> rel ARel l y x.
  Proof.
    intros. destruct ARel;ssa.
    move: (equiv0 l). case. ssa.
  Qed.

Lemma rel_trans : forall A (ARel : myrel A) l x y z, rel ARel l x y -> rel ARel l y z -> rel ARel l x z.
  Proof.
    intros. destruct ARel;ssa.
    move: (equiv0 l). case. ssa. eauto.
  Qed.

Lemma myrel_rule1 : forall (A : Ty) (ARel : myrel [A]) l0 l1, order l0 l1 -> forall a0 a1 : [A], rel ARel l1 a0 a1 -> rel ARel l0 a0 a1.
Proof. intros. de ARel. eauto.
Qed.

Lemma myrel_rule2 : forall (A : Ty) (ARel : myrel [A]), forall l0 l1 : level, order l0 l1 -> forall a : [A], dis ARel l1 a -> dis ARel l0 a.
Proof. intros. de ARel. eauto.
Qed.

Print myrel.

Lemma myrel_rule3 : forall (A : Ty) (ARel : myrel [A]), forall (l : level) (a0 : [A]), dis ARel l a0 -> forall a1 : [A], dis ARel l a1 <-> rel ARel l a0 a1.
Proof. intros. de ARel. 
Qed.

Hint Resolve rel_refl rel_sym rel_trans myrel_rule1 myrel_rule2 myrel_rule3.
Definition eqmaybe_dis {V : Ty} (P: levelPred) (VRel : myrel [V]) l (v : [Option V]) := if v is Some v' then dis VRel l v' else ~ P l.
Definition eqmaybe_aux {V : Ty} (P: levelPred) (VRel : myrel [V]) : presP P -> myrel ([Option V]).
intros.  
    refine (@MyRel _
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

Definition Option_presP : presP (fun _ => True).
  rewrite /presP. eauto.
Qed.

Definition Option_presP_false : presP (fun _ => False).
  rewrite /presP. eauto.
Qed.

Definition Option_presP_top : presP (fun l => l <> \bot).
  rewrite /presP. intros. subst. rewrite /order in H. intro. subst. apply/H0.  rewrite lex0 in H. by apply/eqP.
Qed.

Definition eqmaybe {V : Ty} (VRel : myrel [V]) : myrel ([Option V]).
  apply:eqmaybe_aux. apply VRel. apply: Option_presP.
Defined.

Definition eqmaybe_top {V : Ty} (VRel : myrel [V]) : myrel ([Option V]).
  apply:eqmaybe_aux. apply VRel. apply: Option_presP_top.
Defined. 


Definition aware (V : Ty) (VRel : myrel [V]) (v : [V]) : levelPred
  := fun l => (forall v', rel VRel l v v' -> v = v' /\ ~ dis VRel l v').
(*Definition boolRel : myrel ([Bool]) := semiprivateRel Bool.*) (*publicRel Bool.*)

(*Definition Option_presP : presP (fun l => @aware Bool (publicRel Bool) true l).
  rewrite /presP. eauto.
Defined.*)

(*Definition eqmaybe_swi {V : Ty} (VRel : myrel [V]) : myrel ([Option V]).
  apply:eqmaybe_aux. apply VRel. apply: Option_presP.
Defined.*)

(*Definition Option_presP : presP (fun _ => False).
  rewrite /presP. eauto.
Qed.*)

(*Definition eqmaybe_maybe {V : Ty} (VRel : myrel [V]) : myrel ([Option V]).
  apply:eqmaybe_aux. apply VRel. apply:Option_presP.
Defined.*)

Definition eqmaybe_false {V : Ty} (VRel : myrel [V]) : myrel ([Option V]).
  apply:eqmaybe_aux. apply VRel. apply:Option_presP_false.
Defined. 

Fixpoint to_rel (ty : Ty): myrel [ty]:=
      match ty as x return myrel [x] with
    | TInput => publicRel TInput
    | THandlerOutput => semiprivateRel THandlerOutput
    | TTypeSyscall => semiprivateRel TTypeSyscall                                 
    | TInterrupt => semiprivateRel TInterrupt
    | Option t => eqmaybe (to_rel t)
    | Times t0 t1 => eqpair_LR (to_rel t0) (to_rel t1)
(*    | Times_L t0 t1 => eqpair_L (to_rel t0) (to_rel t1)
    | Times_R t0 t1 => eqpair_R (to_rel t0) (to_rel t1)
      | Times_LR t0 t1 => eqpair_LR (to_rel t0) (to_rel t1)
                                    *)
      | Sum t0 t1 => eqsum_LR (to_rel t0) (to_rel t1)
      | Bool => boolRel
    | ty' => publicRel ty'
    end.


(*Definition to_rel2 (ty : Ty): myrel [ty].
  refine(
    match ty as x return myrel [x] with
      | Times ((Times (Option Nat) (Times Nat Nat))) InputTypeRel => eqpair (to_rel ((Times (Option Nat) (Times Nat Nat)))) (to_rel InputTypeRel)
      | ty' => to_rel ty'
    end).
Defined.*)


Definition to_rel_locked := to_rel.

Notation "# A" := (to_rel_locked A)(at level 5).
Lemma to_rel_unlock : to_rel_locked = to_rel. done.
Qed.
Opaque to_rel_locked.
Ltac ulock := rewrite to_rel_unlock.




(*Definition Clause1 (I O : Ty) (l : level) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  forall i s', s = (Cons (inl i) s') -> dis I l i -> R s' p.

Definition Clause2 (I O : Ty) (l : level) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  (forall i, dis I l i -> exists p', reduceI p i p' /\ R s p').

Definition Clause3 (I O : Ty) (l : level) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  forall i s', s = (Cons (inl i) s') -> (forall i', rel I l i' i -> exists p', reduceI p i' p' /\ R s' p').

Definition Clause4 (I O : Ty) (l : level) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  forall o s', s = (Cons (inr o) s') -> exists o', rel O l o' o /\ exists p', reduceO p o' p' /\ R s' p'.

Variant SimulationF (I O : Ty) (l : level) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | SI s p : Clause1 l R s p ->
             Clause2 l R s p ->
             Clause3 l R s p ->
             Clause4 l R s p ->
             SimulationF l R s p.

Ltac rc := rewrite /Clause1 /Clause2 /Clause3 /Clause4.
Lemma monotone_Clause1 {I O : Ty}  l :  monotone2 (@Clause1 I O l).
Proof.
intro. ssa. rc. eauto.
Qed.

Lemma monotone_Clause2 {I O : Ty}  l :  monotone2 (@Clause2 I O l).
Proof.
  intro. rc. ssa. 
  move: (IN _ H). ssa. eauto.
Qed.

Lemma monotone_Clause3 {I O : Ty}  l :  monotone2 (@Clause3 I O l).
Proof.
  intro. rc. ssa. subst.
  move: (IN _ _ Logic.eq_refl _ H0). ssa. eauto.
Qed.

Lemma monotone_Clause4 {I O : Ty}  l :  monotone2 (@Clause4 I O l).
Proof.
  intro. rc. ssa. subst.
  move: (IN _ _ Logic.eq_refl). ssa. eauto.
  exists x. ssa. eauto.
Qed.


Lemma monotone_SimulationF {I O : Ty}  l:  monotone2 (@SimulationF I O l).
Proof.
rewrite /monotone2. ssa.
inv IN.
eapply SI.
eapply monotone_Clause1. eauto. eauto.
eapply monotone_Clause2. eauto. eauto.
eapply monotone_Clause3. eauto. eauto.
eapply monotone_Clause4. eauto. eauto.
Qed.
Hint Resolve monotone_SimulationF : paco.

Definition simulation {I O : Ty} l s p := paco2 (@SimulationF I O l) bot2 s p.*)
(*Arguments simulation : clear implicits.*)
Inductive NotSim {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) : Stream ([I] + [O]) -> Proc I O -> Prop :=
| NS1 i s p : dis IRel l i -> NotSim l IRel ORel s p -> NotSim l IRel ORel (Cons (inl i) s) p
| NS2 i s p : dis IRel l i -> (forall p', reduceI p i p' -> NotSim l IRel ORel s p') -> NotSim l IRel ORel s p
| NS3 i s p : (forall p', (exists i', rel IRel l i i' /\ reduceI p i' p') ->  NotSim l IRel ORel s p') -> NotSim l IRel ORel (Cons (inl i) s) p
| NS4 o s p : (forall p' o', rel ORel l o o' -> reduceO p o' p' -> NotSim l IRel ORel s p') -> NotSim l IRel ORel (Cons (inr o) s) p.
    
Ltac pc := pclearbot.
Definition streampred (I O : Set) l (IRel : myrel I) (ORel : myrel O) (s : Stream (I + O))  := ForAll (fun x => match x with | Cons (inl x') _ => dis IRel l x' | Cons (inr x') _ => dis ORel l x' end) s.

Lemma rel_eq : forall (I : Set) (IRel : myrel I) (x : I) l, rel IRel l x x.
Proof.
  intros. de IRel. ssa.
  move: (equiv0 l). case. move=> Hr _ _. apply Hr.
Qed.
Hint Resolve rel_eq.

Ltac rc_in H := move: H;rc=>H.


  Check simulation.

  Lemma toNotSim : forall {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) s (p : Proc I O), NotSim l IRel ORel s p -> ~simulation IRel ORel l s p.
  Proof.
  move=> I O l IRel ORel s p H Hsim.
  elim: H Hsim;intros.
  - punfold Hsim. inv Hsim.
    clear H3 H4 H5. rc_in H2. 
    case: (H2 _ _ Logic.eq_refl H)=>//. 
  - punfold Hsim. inv Hsim.
    clear H2 H4 H5. rc_in H3.
    case: (H3 _ H)=>p1 [] Hred [] Hsim'//;eauto.
  - punfold Hsim. inv Hsim.
    clear H1 H2 H4. rc_in H3.
    case: (H3 _ _ Logic.eq_refl _ (rel_eq IRel i l))=>p1 [] Hred []// Hsim'.
    eapply H0. 2:eauto. exists i. eauto.
  - punfold Hsim. inv Hsim.
    clear H1 H2 H3. rc_in H4. pc.
    move: (H4 _ _ Logic.eq_refl). ssa.
    apply rel_sym in H1. 
    
    eapply H0. eauto. eauto. pc. done.
Qed.

  Variant ObliviousF {I O : Ty} (ORel : myrel [O]) (l : level) (R : Proc I O -> Prop) : Proc I O -> Prop :=
  OF1 p : (forall i p', reduceI p i p' -> R p') -> (forall o p', reduceO p o p' -> R p' /\ dis ORel l o) ->  ObliviousF ORel l R p.

Lemma monotone_ObliviousF {I O : Ty} (ORel : myrel [O]) (l : level) : monotone1 (@ObliviousF I O ORel l).
Proof.
intro;ssa.
inv IN;eauto.
econ;eauto.
intros.
move: (H0 _ _ H1). case. eauto.
Qed.
Hint Resolve monotone_ObliviousF : paco.

Definition oblivious {I O : Ty} (ORel : myrel [O]) p : levelPred := fun l => paco1 (@ObliviousF I O ORel l) bot1 p.

(*Inductive NotObl (I O : Ty) (l : level) : Proc I O -> Prop :=
  | NotObl_I p i p' : reduceI p i p' -> NotObl l p' -> NotObl l p
  | NotObl_O p o p' : reduceO p o p' -> NotObl l p' -> NotObl l p                                                          
  | NotObl_dis p o : dis O l o -> NotObl l p.*)

Definition aware_or_oblivious  {I O : Ty} (ORel : myrel [O]) (o : [O]) (p : Proc I O) : levelPred := fun l => aware ORel o l \/ oblivious ORel p l.


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
    | |- reduceI (@sta _ _ _ _ _ ?v _) _ _ => idtac "state" v;apply: reduce_staI
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

Ltac appTrace := apply: traceI || apply: traceO.


Ltac bundle :=
  (pfold;
  first [ appTrace | rewr;appTrace ];
   first (do ? reduce_tac));controlled_eauto;simpl.

Ltac bundle_v :=
  (pfold;
  first [ appTrace | rewr;appTrace ];
  first (do ? reduce_tac_v));simpl;try econ.




Definition f_NI {I O :Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O]) := forall (l : level) (i i' : [I]), rel IRel l i i' -> rel ORel l (f i) (f i').
Definition f_PU {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O]) := forall l (i : [I]), dis IRel l i -> dis ORel l (f i).
Definition f_NI_PU {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O])  := f_NI IRel ORel f /\ f_PU IRel ORel f.
Definition fv_NI (I O V: Ty) (IRel : myrel [I]) (ORel : myrel [O]) (VRel : myrel [V])  (f : [I] -> [V] -> [O]) := forall l (i i' : [I]), rel IRel l i i' -> forall (v v' : [V]), rel VRel l v v' -> rel ORel l (f i v) (f i' v').
Definition f_EP (I V: Ty) (IRel : myrel [I]) (VRel : myrel [V]) (f : [I] -> [V] -> [V]) := forall l i, dis IRel l i -> forall v, rel VRel l (f i v) v. (*equivalence preserving*)

(*Definition f_NI {I O :Ty} (f : [I] -> [O]) := forall (l : level) (i i' : [I]) (o o' : [O]), rel I l i i' -> rel O l (f i) (f i').
Definition f_PU {I O : Ty} (f : [I] -> [O]) := forall l (i : [I]), dis I l i -> dis O l (f i).
Definition f_NI_PU {I O : Ty} (f : [I] -> [O]) := f_NI f /\ f_PU f.
Definition fv_NI (I O V: Ty) (f : [I] -> [V] -> [O]) := forall l (i i' : [I]), rel I l i i' -> forall (v v' : [V]), rel V l v v' -> rel O l (f i v) (f i' v').
Definition f_EP (I V: Ty) (f : [I] -> [V] -> [V]) := forall l i, dis I l i -> forall v, rel V l (f i v) v. (*equivalence preserving*)*)

(*Admitted theorems*)

Lemma out_NI : forall I O (IRel : myrel [I]) (ORel : myrel [O]) (o : [O]), @NI I O IRel ORel (out o).
Proof.
  intros. rewrite /NI.
  move=>l. pcofix CIH.
  ssa. punfold H0. inv H0.
  - pc. match_dd.
    pfold. con.
    * rc. intros. inv H. right. apply CIH. done.
    * rc. intros. exists (@out _ _ o). con. eauto;con. right. apply CIH.
      pfold. done.
    * rc. intros. exists (@out _ _ o). con. eauto.
      right. inv H. eauto.
    * rc. intros. inv H.
  - pc. match_dd.
    pfold. con.
    * rc. intros. inv H.
    * rc. intros. exists (@out _ _ o). con. eauto. right. apply CIH.
      pfold. done.
    * rc. intros. exists (@out _ _ o). con. eauto.
      right. inv H. eauto.
    * rc. intros. inv H.
      exists o0. ssa. exists (@out _ _ o0). con. eauto. eauto.
Qed.

(*Variant mapTraceF (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (IRel : myrel [I]) (IRel' : myrel [I']) (ORel : myrel [O]) (ORel' : myrel [O']) (p : Proc I' O)
  (R :  Stream ([I'] + [O]) -> Stream ([I] + [O']) -> Prop):
  Stream ([I'] + [O]) -> Stream ([I] + [O']) ->  Prop :=
  
  | MTF0 i s s' : R s s' -> mapTraceF f g IRel IRel' ORel ORel' p R (Cons (inl (f i)) s) (Cons (inl i) s')
  | MTF1 o s s' : R s s' -> mapTraceF f g IRel IRel' ORel ORel' p R (Cons (inr o) s) (Cons (inr (g o)) s').


Lemma mapTraceF_mon (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (IRel : myrel [I]) (IRel' : myrel [I']) (ORel : myrel [O]) (ORel' : myrel [O']) (p : Proc I' O) :
  monotone2 (mapTraceF f g IRel IRel' ORel ORel' p).
  intro. intros. inv IN. con. eauto. con. eauto.
Qed.
Hint Resolve mapTraceF_mon : paco.

Definition mapTrace (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (IRel : myrel [I]) (IRel' : myrel [I']) (ORel : myrel [O]) (ORel' : myrel [O']) (p : Proc I' O) s s' :=
  paco2 (mapTraceF f g IRel IRel' ORel ORel' p) bot2 s s'.

Lemma to_mapTrace : forall (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (IRel : myrel [I]) (IRel' : myrel [I']) (ORel : myrel [O]) (ORel' : myrel [O']) (p : Proc I' O),
    trace s' (map f g p) -> ex*)

Lemma map_NI : forall (I I' O O' : Ty) (p : Proc I' O) (f : [I] -> [I']) (g : [O] -> [O']) (IRel : myrel [I]) (IRel' : myrel [I']) (ORel : myrel [O]) (ORel' : myrel [O']),
    f_NI IRel IRel' f -> f_PU IRel IRel' f -> f_NI ORel ORel' g ->
    NI IRel' ORel p ->     
    NI IRel ORel' (map f g p).
Proof.
Admitted. 

Lemma sta_NI : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O]),
    fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f -> f_EP IRel VRel f ->
    NI (eqpair_R VRel IRel) ORel p ->
    NI IRel (eqpair VRel ORel) (sta f g v p).
Admitted.

 (*fixed typo in paper: In conclusion, replaced I with Bool * I  *) 
Theorem swi_NI : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (BRel : myrel [Bool]) p b,
(forall l, aware BRel true l \/  oblivious (eqpair_R BRel ORel) p l ) -> NI IRel (eqpair_LR BRel ORel) p ->                                
NI (eqpair_LR BRel IRel) (eqmaybe ORel) (swi b p).
 Admitted.

Theorem maybe_NI : forall (I O :Ty) (IRel : myrel [I]) (ORel : myrel [O]) p, NI IRel ORel p -> NI (eqmaybe_false IRel) ORel (maybe p).
Admitted.

Theorem loop_NI : forall (I : Ty) (IRel : myrel [I]) p, NI IRel IRel p -> NI IRel IRel (loop p).
Admitted.

Theorem par_NI : forall (I O1 O2 : Ty) (IRel : myrel [I]) (ORel1 : myrel [O1]) (ORel2 : myrel [O2]) p1 p2,
    NI IRel ORel1 p1 -> NI IRel ORel2 p2 -> NI IRel (eqpair ORel1 ORel2) (par p1 p2).
Admitted.


(*par_swi is incorrect, it is always receiving input. It needs to be wrapped in maybe, such as is seen in scheduled_p*)
(*Hint Extern 1 (Ty) => constructor : core.*)
(*Hint Extern 1 ([ ?T ]) => econstructor : core.
Hint Extern 1 ([ ?T * ?T2 ]) => apply: Times_R*)
(*Print Ty.
Hint Extern 5 ([ ?T ]) =>
  (* We 'refine' the goal by providing a specific constructor 
     wrapped in the interpretation notation *)
  first [ 
    refine [ Times _ _ ] | 
    refine [ Times_LR _ _ ] | 
    refine [ Times_R Bool _ ] 
  ];
                simpl : core.


Hint Extern 1 ([ Times_R _ _ ]) =>
       unfold interp; simpl : core.
*)


Hint Extern 1 =>
  match goal with
  | [ |- [ ?target ] ] => 
      is_evar target;  (* If the type index is unknown *)
      (* Force the index to be a pair-producing constructor *)
      unshelve (refine [ _ ]); [ constructor | simpl ]
  end : core.

Definition par_swiI {I1 I2 O1 O2} (b:bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2)
  := par
      (swi b (@map (Times _ _) _ _ _ fst (fun x => (false,x) : [Times Bool _]) p1))
      (swi (negb b) (@map (Times _ _) _ _ (Times Bool _) snd (fun x => (false,x)) p2)).


(*Definition par_swiI {I1 I2 O1 O2} (b:bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2)
  := par
      (swi b (@map (Times _ _) _ _ (Times_R Bool _) fst (fun x => (false,x)) p1))
      (swi (negb b) (@map (Times _ _) _ _ (Times_R Bool _) snd (fun x => (false,x)) p2)).*)


(*Definition par_swiI {I1 I2 O1 O2} (b:bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2)
  : Proc (_ Bool (Times I1 I2)) (_ (Option O1) (Option O2)) :=
    par
      (swi b (@map (Times _ _) _ _ (Times_R Bool _) fst (fun x => (false,x)) p1))
      (swi (negb b) (@map (Times _ _) _ _ (Times_R Bool _) snd (fun x => (false,x)) p2)).*)


(*Not used for anything*) Check sta.
Definition scheduled_p (I O : Ty) (b : bool) (p : Proc I O) :=
  @map _ _ (Times _ _) _ id snd (*drop state*)
    (@sta (Times Bool _) _ Bool (fun i v => xor (fst i) v) (fun o v => v) b (*track swi flag*)
       (@map (Times _ (Times _ _))  (Times _ (Times _ _)) _ _ (fun i => (fst (snd i),(fst i,snd (snd i)))) id (*(v,(b,i)) -> (b,(v,i))*)
          (swi b (@map (Times Bool _) (Option _) _ (Times Bool _) (fun i => if fst i then Some (snd i) else None) (fun o => (false,o)) (*if b then send input to p*)
                    (maybe p))))).


(*Comment: Maybe prove this? We need it for example 2 (shows noninterference)*)
(*Lemma par_swiI_NI : forall (I1 I2 O1 O2 : Ty) (b : bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (IRel1 : myrel [I1]) (IRel2 : myrel [I2]) (ORel1 : myrel [O1]) (ORel2 : myrel [O2]),
     NI IRel1 ORel1 p1 -> NI IRel2 ORel2 p2 -> NI (eqpair_LR boolRel (eqpair IRel1 IRel2)) (eqpair (eqmaybe_swi ORel1) (eqmaybe_swi ORel2)) (par_swiI b p1 p2).
Proof. Admitted.*)

(*sta_swi b n f p:
 (i == n,I') -> enables p
 (i <> n,I') -> disables p
 f projects input from pair e.g. f (I1,I2) = I1
 maybe is used to disgard input to p when i<>n.
 *)
Check swi.
Definition sta_swi (I' I O : Ty) (b : bool) (n : nat) (f : [I'] -> [I]) (p : Proc I O) :=
  @map (Times Nat _) (Times Bool (Option _)) (Option _) _ (fun x => let b := fst x == n in (b, if b then Some (f (snd x)) else None)) id
       (swi b (@map _ _ _ (Times Bool _)
                    id
                    (fun o => (true,o))
                    (maybe p)
  )).

(*Definition sta_swi (I' I O : Ty) (b : bool) (n : nat) (f : [I'] -> [I]) (p : Proc I O) :=
@map (Times Nat _) (Times Bool _) (Times _ _) _ (fun x => (fst x == n, f (snd x))) snd (*apply f to input before entering sta because it caused issues with the mitigator NI proof*)
  (@sta (Times Bool _) _ Bool
       (fun i v => xor (fst i) v)
       (fun o v => false)
       b
       (swi b (@map (Times Bool _) (Option _) _ (Times Bool _)
                    (fun i => if fst i then Some (snd i) else None)
                    (fun o => (true,o))
                    (maybe p)
  ))).*)

(*Definition sta_swi_base (I O : Ty) (b : bool) (p : Proc I O) :=
  @map _ _ (Times Bool _) (Option _) id (fun bo => if fst bo then Some (snd bo) else None )
    ((@sta (Times Bool _) _ Bool
       (fun i v => xor (fst i) v)
       (fun o v => false)
       b
       (@map (Times Bool (Times Bool _)) (Option _) _ _
                    (fun i => if fst i then Some (snd (snd i)) else None)
                    id
                    (maybe p))
  )).*)

(*Definition sta_swi_base (I O : Ty) (b : bool) (p : Proc I O) :=
  @map _ _ (Times Bool _) (Option _) id (fun bo => if fst bo then Some (snd bo) else None ) ((@sta (Times Bool _) _ Bool
       (fun i v => xor (fst i) v)
       (fun o v => false)
       b
       (@map (Times Bool (Times Bool _)) (Option _) _ _
                    (fun i => if fst i then Some (snd (snd i)) else None)
                    id
                    (maybe p))
  )).*)

(*Got to here...*)
(*Lemma sta_swi_base_NI I O (p : Proc I O) (IRel : myrel [I]) (ORel : myrel [O]) b :
  NI (eqpair (privateRel _) IRel)
    (eqpair (privateRel _) ORel) (
      sta_swi_base b p).*)


(*Definition sta_swi (I' I O : Ty) (b : bool) (n : nat) (f : [I'] -> [I]) (p : Proc I O) :=
  @map (Times Nat _) (Times Bool _) _ _ (fun x => (fst x == n, f (snd x))) id
       (sta_swi_base b p).*)


(*Definition sta_swi_base (I O : Ty) (b : bool) (p : Proc I O) :=
  (@sta (Times Bool _) _ Bool
       (fun i v => xor (fst i) v)
       (fun o v => false)
       b
       (swi b (@map (Times Bool _) (Option _) _ (Times Bool _)
                    (fun i => if fst i then Some (snd i) else None)
                    (fun o => (true,o))
                    (maybe p)
  ))).



Definition sta_swi (I' I O : Ty) (b : bool) (n : nat) (f : [I'] -> [I]) (p : Proc I O) :=
@map (Times Nat _) (Times Bool _) (Times _ _) _ (fun x => (fst x == n, f (snd x))) snd (*apply f to input before entering sta because it caused issues with the mitigator NI proof*)
  (@sta (Times Bool _) _ Bool
       (fun i v => xor (fst i) v)
       (fun o v => false)
       b
       (swi b (@map (Times Bool _) (Option _) _ (Times Bool _)
                    (fun i => if fst i then Some (snd i) else None)
                    (fun o => (true,o))
                    (maybe p)
  ))).*)


(*Lemma sta_swi_NI I' I O b n (p : Proc I O) (f : [I'] -> [I]) (IRel' : myrel [I']) (ORel : myrel [O]) : NI (eqpair (privateRel _) IRel) (eqmaybe_swi ORel) (sta_swi b n f p).*)




Definition par_swiI3 {I1 I2 I3 O1 O2 O3} (n : nat) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (p3 : Proc I3 O3)
  : Proc (Times Nat (Times I1 (Times I2 I3))) (Times (Option O1) (Times (Option O2) (Option O3))) :=
    par
      (@sta_swi (Times _ _) _ O1 (n == 0) 0 fst p1)
      (par
      (@sta_swi (Times _ (Times _ _)) _ O2 (n == 1) 1 (fun x => fst (snd x)) p2)
      ((@sta_swi (Times _ (Times _ _)) _ O3 (n == 2) 2 (fun x => snd (snd x)) p3))). 



(*Types used in all examples*)
Definition ExInputType := Times TInput TInput.
Definition ExOutputType := Times (Option TOutput) (Option TOutput).

Definition streamType := Stream ([TInput] + (([ExOutputType]))).



Definition OutputRel : myrel ([TOutput]).
  refine (@MyRel _
            (fun l a => l = \bot /\ a = Step )
            (fun l a b => a = b) _ _ _ _).
  intros.
  done.
  intros. ssa. subst. subst. subst.
  Search _ order.
  move/order_bot : H. move=>->. done.
  intros. ssa. subst. con.
  ssa.
  ssa.
Defined.

Definition Output_option_presP : presP (fun l => l = \top).
  rewrite /presP. intros. rewrite /order in H. subst.
  rewrite le1x in H. by rewrite (eqP H).
Defined.

(*Definition Output_option : myrel ([Option TOutput]) := eqmaybe OutputRel.

Definition Output_option_prod : myrel ([ExOutputType]).
  apply publicRel.
(*  apply eqpair. apply Output_option. apply Output_option.*)
  Defined.*)







(**Examples*)
(*In all examples, private means distinguished for \low*)

Print Step.
(*Example 1: Interference
  Scheduler switches between p_low and p2 based on secret input
  Input  := Skip (public) | DiskRead (private)
  Output := Idle (public) | Step (private)
 *)
Module Example1.
(*Process*)
Definition p_high := @out TInput TOutput Step.
Definition p_low := @out TInput TOutput Idle.
Definition process_pool := par_swiI false p_high p_low. (*both p_high and p_low receive inputs no matter who was scheduled. This is because par_swiI does not filter input. p_high and p_low don't change state based on input so it is fine in this example*)

Definition scheduler (p : Proc (Times Bool (Times TInput TInput)) (Times (Option TOutput) (Option TOutput))) :=
  @map _ (Times Bool (Times TInput TInput)) _ _ (fun (i : [TInput]) => (i == DiskRead,(i,i))) id p.

(*Trace*)
Definition newtraceF_simple (newtrace : streamType) := Cons (inr (None, Some Idle))
                                                         (Cons (inl (DiskRead))
                                                           (Cons (inr (Some Step,None))
                                                                  (Cons (inl (DiskRead)) newtrace))).
CoFixpoint newtrace_simple := newtraceF_simple newtrace_simple.

Lemma newtrace_simple_eq : newtrace_simple = newtraceF_simple newtrace_simple.
Proof.
rewrite {1}/newtrace_simple.
rewrite {1}(coseq_match (cofix newtrace : streamType := newtraceF_simple newtrace)).
simpl.
rewrite /newtraceF_simple.
do ? f_equal.
Qed.


(*Trace derivation*)
Ltac rewr ::=  (try rewrite newtrace_simple_eq); rewrite /newtraceF_simple /process_pool /par_swiI /scheduler /p_high /p_low.
Check process_pool.
Lemma simple_trace : trace newtrace_simple (scheduler process_pool).
Proof.
  pcofix CIH.
  rewr.
  bundle. left.
  bundle. left.
  bundle. left.
  bundle. right.
  swi_instans. eauto.
Qed.

Definition InputRel : myrel ([TInput]). 
  refine (@MyRel _
            (fun l a => l = \bot /\ a = DiskRead)
            (fun l a b => a = b) _ _ _ _).
  intros.
  done.
  intros. ssa. subst. subst. subst.
  Search _ order.
  move/order_bot : H. move=>->. done.
  intros. ssa. subst. con.
  ssa.
  ssa.
Defined.  

(*NotSim*)
Example counterexample : NotSim \bot InputRel (publicRel _) newtrace_simple (scheduler process_pool).
Proof. 
  rewrite newtrace_simple_eq /newtraceF_simple.
  apply:NS4. ssa. de o'. subst.
  
  apply: NS2. instantiate (1:= (DiskRead)).
  ssa.

  intros. match_dd.

  apply: NS3. ssa. de x. subst.
  match_dd.
  
  apply: NS4. ssa. de o'. subst.
  match_dd.
Qed.

(*Not NI*)
Example example_not_NI :  ~ NI InputRel (publicRel _) (scheduler process_pool).
Proof.
  rewrite /NI. ssa. intro.

  apply/toNotSim. apply/counterexample.
  apply/H. apply simple_trace.
Qed.
End Example1.


Definition TraceF_specific := (@TraceF TInput (Times (Option TOutput) (Option TOutput))).
Lemma specific_monotone : monotone2 TraceF_specific.
  apply (@monotone_TraceF TInput (Times (Option TOutput) (Option TOutput))).
Qed.
Hint Resolve specific_monotone : paco.




Coercion to_rel_locked : Ty >-> myrel.

Arguments NI : clear implicits.
Arguments NI I O IRel ORel.
Lemma NI_swap_rel : forall I O (p : Proc I O) (IRel : myrel [I]) (ORel ORel' : myrel [O]), (forall l x y, rel ORel l x y <-> rel ORel' l x y) -> NI I O IRel ORel p -> NI I O IRel ORel' p.
Proof.
  intros. intro. intros. eapply H0 in H1.
  move: H1. instantiate (1:= l).
  intros. apply/paco2_imp. apply monotone_SimulationF.
  2:eauto. ssa.
  inv H2;econ;eauto.
  rewrite /Clause4. ssa. apply H6 in H7. ssa. exists x.
  ssa;eauto. apply/H. done.
Qed.  

(*Lemma NI_add_L : forall I V O (p : Proc I (Times V O)) IRel,
    NI I (Times V O) IRel (eqpair_R (to_rel V) (to_rel O)) p ->
    NI I (Times V O) IRel (eqpair_LR (to_rel V) (to_rel O)) p.
Proof.
  intros. 
  apply/simulation_equiv.
  move/simulation_equiv : H.
  intros. apply/NI_swap_rel. 2:eauto.
  ssa.
Qed.

Lemma NI_add_R : forall I V O (p : Proc I (Times V O)) IRel,
    NI I (Times V O) IRel (eqpair (to_rel V) (to_rel O)) p ->
    NI I (Times V O) IRel (eqpair_R (to_rel V) (to_rel O)) p.
Proof.
  intros. 
  apply/simulation_equiv.
  move/simulation_equiv : H.
  intros. apply/NI_swap_rel. 2:eauto.
  ssa.
Qed.*)

(*Lemma SimulationF_I_imp : forall I O l (IRel IRel' : myrel [I]) (ORel : myrel [O]) R s p,
    (forall l x, dis IRel' l x -> dis IRel l x) ->
    (forall l x y, rel IRel l x y <-> rel IRel' l x y) ->
    SimulationF l IRel ORel R s p ->
    SimulationF l IRel' ORel R s p.
Proof.
  intros. inv H1. con;eauto.
  rewrite /Clause1. ssa. eauto.
  rewrite /Clause2. ssa. 
  rewrite /Clause3. ssa.
  move: H4. rewrite /Clause3. ssa. eapply H4 in H6;eauto. apply/H0. done.
Qed.*)

Lemma SimulationF_I_imp : forall I O l (IRel IRel' : myrel [I]) (ORel : myrel [O]) R s p,
    (forall l x, dis IRel' l x -> dis IRel l x) ->
    (forall l x y, rel IRel' l x y -> rel IRel l x y) ->
    SimulationF l IRel ORel R s p ->
    SimulationF l IRel' ORel R s p.
Proof.
  intros. inv H1. con;eauto.
  move: H2. rewrite /Clause1. intros.
  apply/H2. eauto. eauto.
  move: H3. rewrite /Clause2. intros.
  apply H in H6. apply H3 in H6. ssa.
  econ. con. eauto. done.
  move: H4.
  rewrite /Clause3. intros.
  eapply H4 in H6. ssa. econ. eauto. eauto.
Qed.

Lemma NI_I_imp : forall I O (IRel IRel' : myrel [I]) (ORel : myrel [O]) R,
    (forall l x, dis IRel' l x -> dis IRel l x) ->
    (forall l x y, rel IRel' l x y -> rel IRel l x y) ->
    NI _ _ IRel ORel R ->
    NI _ _ IRel' ORel R.
Proof.
  intros. 
  intros. rewrite /NI. intros. eapply H1 in H2.
  move: H2. instantiate (1:=l).
  apply:paco2_imp. apply monotone_SimulationF.
  intros. apply/SimulationF_I_imp. 3:eauto. eauto. eauto.
Qed.


Lemma SimulationF_O_imp : forall I O l (IRel : myrel [I]) (ORel ORel' : myrel [O]) R s p,
(*    (forall l x, dis ORel l x -> dis ORel' l x) ->*)
    (forall l x y, rel ORel l x y -> rel ORel' l x y) ->
    SimulationF l IRel ORel R s p ->
    SimulationF l IRel ORel' R s p.
Proof.
  intros. inv H0. con;eauto.
  move: H4.
  rewrite /Clause4. intros. apply H4 in H5. ssa.
  econ. con. apply/H. apply:H5. econ. con. eauto. done.
Qed.

Lemma NI_O_imp : forall I O (IRel : myrel [I]) (ORel ORel' : myrel [O]) R,
(*    (forall l x, dis ORel l x -> dis ORel' l x) ->*)
    (forall l x y, rel ORel l x y -> rel ORel' l x y) ->
    NI _ _ IRel ORel R ->
    NI _ _ IRel ORel' R.
Proof.
  intros. 
  intros. rewrite /NI. intros. eapply H0 in H1.
  move: H1. instantiate (1:=l).
  apply:paco2_imp. apply monotone_SimulationF.
  intros. apply/SimulationF_O_imp. 2:eauto. eauto. 
Qed.

(*Lemma iNI_add_L : forall I V O (p : Proc (Times V I) O) VRel IRel ORel,
    NI (Times V I) O (eqpair_R VRel IRel) ORel p ->
    NI (Times V I) O (eqpair_LR VRel IRel) ORel p.
Proof.
  intros. 
  apply/simulation_I_imp. 3:eauto.
  ssa. ssa.
Qed.*)


(* Example removed for now. We can add it later if we prove NI for par_swiI
  
Example 2: Non-interference
 round-robin between p_high and p_low
 input is public*)
(*Module Example2.
Definition p_high := (@out TInput TOutput Step). 
Definition p_low := (@out TInput TOutput Idle). 
Definition process_pool := par_swiI false p_high p_low.
Definition scheduler {I O} (p : Proc (Times Bool (Times I I)) O) : Proc I O := @map _ (Times Bool (Times _ _)) _ _ (fun i => (true,(i,i))) id p.


Definition InputRel : myrel ([TInput]). 
  refine (@MyRel _
            (fun l a => l = \bot /\ a = DiskRead)
            (fun l a b => a = b) _ _ _ _).
  intros.
  done.
  intros. ssa. subst. subst. subst.
  Search _ order.
  move/order_bot : H. move=>->. done.
  intros. ssa. subst. con.
  ssa.
  ssa.
Defined.  
(*Definition InputRelPublic : myrel ([TInput]) := publicRel TInput.*)

Example hl_lp_NI : @NI TInput (Times (Option TOutput) (Option TOutput))
                     InputRel (*InputRel*)
                     (eqpair (eqmaybe_swi (publicRel TOutput)) (eqmaybe_swi (publicRel TOutput))) (*OutputRel*)
                     (scheduler process_pool).
Proof. simpl.
  rewrite /scheduler.
  eapply map_NI.
  eapply par_swiI_NI.
  apply out_NI.
  apply/simulation_I_imp. shelve. shelve.
  apply out_NI.
  instantiate (1:= InputRel). instantiate (1:= InputRel).
  intro. intros. ssa.
  intro. intros. simpl in H. simpl. 
  rewrite /f_NI. intros. rewrite /InputRel /= in H. simpl.

  rewrite /f_PU. ssa. simpl.
  rewrite /f_NI. intros. eauto.
Qed.
End Example2.*)



(*Example 3
  Consists of two sub-examples (a) and (b)
  (a) round robin between low_p, high_p. Execution of either process is disrupted by hardware interrupt that schedules handler
  (b) round robin between low_p and high_p. Execution is never disrupted. Instead handler is scheduled at each context switch
 *)
Module Example3.
(*Shared definitions for examples (a) and (b)*)  
Definition low_p := @out Unit TPublicOutput GetRequest.
Definition high_p := @out THandlerOutput TTypeSyscall Syscall. 

(*Handler is complicated because we need to do 2 things:
1) Switch what we output based on whether an input has happened since the last output
2) reset the state after the output has been performed

in sta, the state cannot be inspected in the making of the output, resetting the state therefore removes the information we would need to distinguish states.
Using the loop construct we can turn "on" the Notify output by receiving an input. Sending the Notify output will due to the loop construct, create a new input, tagged with inr, which resets the state
 *)
Definition alternate_generic (A B: Ty) (x y : [B]) := @map _ (Sum _ _) (Sum _ (Times Bool Unit)) B 
                        inl
                        (fun o => if o is inr (true,tt) then x else y)
                        (@loop (Sum A (Times Bool Unit))
                        (@map (Sum A _) _ _ (Sum _ _) id (fun o => inr o)
                        ((@sta (Sum _ _) _ Bool
                           (fun i v => if i is inl _ then true else false)
                           (fun o v => v)
                           false
                           (@out (Times Bool _ ) Unit tt)
                        )))).
Definition handler := @alternate_generic TInterrupt THandlerOutput Notify Nothing.

Definition process_pool := par_swiI3 0 (maybe low_p) (maybe high_p) (maybe handler). (*we end up with a double maybe because par_swiI3 also wraps maybe around the processes. We want this. The outer maybe discards irrelevant input while the latter maybe allows us to write default values in our traces, such as (None,(Some i),None) for input to high process*)

(* Scheduler *) Print Option.
Definition InputType := (Times (Option Unit) (Times (Option THandlerOutput) (Option TInterrupt))).
Definition NInputType := Times Nat InputType.
Definition OutputType :=  (Times (Option TPublicOutput) (Times (Option TTypeSyscall) (Option THandlerOutput))).
Definition IOType := Sum InputType OutputType.


Definition outf : [IOType] -> [OutputType] :=  (fun x => match x with | inl _ => (None,(None,None)) | inr y => y end).
Print InputType. Print Interrupt.
Print OutputType.
Definition route_aux (state_type : Ty) (x : [IOType]) :=
                          match x with
                          | inl i' => i' (*inl = input*)
                          | inr (_,(x,y)) => (None,(y,None)) (*inr = output from handler rerouted as input to high process. The important case is inr (None,None,Some h) which maps to (None,Some h,None). The more general pattern is to ensure that distinugishability is unchanged by the map. This is fine because (Some x,_,_) and (None,_,_) have the same distinguishability *)
                          end.

Definition route (state_type : Ty) (to_schedule : [state_type] -> nat) (x : [Times state_type IOType]) :=
                  (to_schedule (fst x), route_aux state_type (snd x)).

Definition scheduler
  (state_type : Ty)
  (state_in : [IOType] -> [state_type] -> [state_type])
  (state_out : [IOType] -> [state_type] -> [state_type])
  (initial_state : [state_type])
  (to_schedule : [state_type] -> nat)
  (p : Proc NInputType OutputType)  :=
  @map InputType IOType IOType OutputType
    inl
    outf
    (loop (*scheduler needs loop - We can only switch par_swiI3 on input, thus output rerouted as input allows scheduler to count outputs - Outputs is our unit of time*)
       (@map _ _ (Times _ _) _
          id
          snd (*removes state*)
          (@sta _ _ state_type
             state_in
             state_out
             initial_state
             (@map (Times state_type IOType) NInputType OutputType IOType
                (route to_schedule)
                inr
                p
    )))).
(* Scheduler *)


(****  Example (a) ****)
Definition state_type1 := Times Bool (Times Nat Nat).

Definition inc_state1 (v : [state_type1]) :=
  let: (b,(c,n)) := v in if b then v else if c == 0 then (b,(c+1,n)) else (b,(0,(n+1)%%2)). (* low process: n = 0 and (b = false)
                                                                                               high process: n = 1 and (b = false)
                                                                                               handler: b = true
                                                                                               two steps per low/high process counted by (c), with c == 0 meaning has the first step been taken yet
                                                                                               nat used for c instead of bool both for readability and in case we increase step count for examples in the future*)

Definition to_schedule1 (v: [state_type1]) : nat :=
  let: (b,(c,n)) := v in if b then 2 else n. (*mapping state state_type1 to the process that should be scheduled*)

Definition state_in1 (o : [IOType]) (v: [state_type1])  : [state_type1] := (*based on output and state, schedule/deschedule handler using the bool flag*)
  let: (b,(c,n)) := v in
  match b,o with
  | false,inl (None,(None, Some i)) => (true,(c,n))
  | true, inr (None,(None, Some Notify)) => (false,(c,n))
  | _,_ => v
  end.

(*schedules the handler on hardware interrupt input*)
Definition bad_scheduler := @scheduler state_type1 state_in1 (fun _ v => inc_state1 v) (false,(0,0)) to_schedule1.

Definition ex3_stream_type := ([InputType] + [OutputType])%type.
(*Definition myTimerInt : ex3_stream_type := inl (None,(None,Some TimerInterrupt)).*)
Definition myDiskInt : ex3_stream_type := inl (None,(None,Some DiskInterrupt)).
Definition myGet  : ex3_stream_type := inr (Some GetRequest,(None,None)).
Definition mySys : ex3_stream_type := inr (None,(Some Syscall,None)).
Definition myNotify : ex3_stream_type := inr (None,(None,Some Notify)).

(*this traces shows the process behavior, two steps for p_low, two_steps for p_high, and whenever there is a TimerInterrupt as input, the next output with be Notify*)
Definition ex3_streamF (s : Stream ex3_stream_type) := Cons myGet
                                                         (Cons myGet
                                                            (Cons mySys
                                                               (Cons mySys
                                                                  (Cons myDiskInt
                                                                     (Cons myNotify s))))).

CoFixpoint ex3_stream := ex3_streamF ex3_stream.

Lemma ex3_stream_eq : ex3_stream = ex3_streamF ex3_stream.
Proof.
rewrite {1}/ex3_stream.
rewrite {1}(coseq_match (cofix newtrace : (Stream ex3_stream_type) := ex3_streamF newtrace)).
simpl.
rewrite /ex3_streamF.
do ? f_equal.
Qed.

(*To show that (bad_scheduler process_pool) is interfering, it suffices to use a shorter trace*)
Definition ex3b_streamF (s : Stream ex3_stream_type) := Cons myGet
                                                         (Cons myGet
                                                            (Cons mySys
                                                               (Cons mySys s))).

CoFixpoint ex3b_stream := ex3b_streamF ex3b_stream.

Lemma ex3b_stream_eq : ex3b_stream = ex3b_streamF ex3b_stream.
Proof.
rewrite {1}/ex3b_stream.
rewrite {1}(coseq_match (cofix newtrace : (Stream ex3_stream_type) := ex3b_streamF newtrace)).
simpl.
rewrite /ex3b_streamF.
do ? f_equal.
Qed.

Ltac rewr ::=  (try rewrite ex3_stream_eq);(try rewrite ex3b_stream_eq); rewrite /par_swiI /bad_scheduler /process_pool /low_p  /ex3_streamF /bad_scheduler /process_pool /par_swiI3 /high_p /handler /sta_swi /scheduler.


Ltac reduce_twice := reduce_once;(try reduce_once);(try eapply Logic.eq_refl).
(*Example simple_trace : trace ex3_stream (bad_scheduler process_pool).
Proof.
  pcofix CIH.
  bundle. left.  (*1 Get*)
  bundle. left.  (*1 Get*)
  bundle. left.  (*2 Sys*)
  bundle. left.  (*3 Sys*)
  bundle. left.  (*4 Timer*)
  bundle. right. (*5 Notify*)
  swi_instans.
  exact CIH.
Qed.*)


Lemma reduceI_trace: forall (A B : Ty) (p : Proc A B) i p' s R, reduceI p i p' -> R s p' -> paco2 TraceF R (Cons (inl i) s) p.
Proof. move=> A B p i p' s R.
       intros. induction H; try solve [ pfold; econ; eauto ].
Qed.

(*Lemma reduceI_trace': forall (A B : Ty) (p : Proc A B) i p' s R, reduceI p i p' -> paco2 TraceF R (Cons (inl i) s) p -> R s p'.
Proof. move=> A B p i p' s R.
       intros. induction H. punfold H0. inv H0. de H4. try solve [ pfold; econ; eauto ].
Qed.*)

Lemma reduceO_trace: forall (A B : Ty) (p : Proc A B) o p' s R, reduceO p o p' -> R s p' -> paco2 TraceF R (Cons (inr o) s) p.
Proof. move=> A B p i p' s R.
       intros. induction H; try solve [ pfold; econ; eauto ].
Qed.

Lemma public_sim : forall (A B : Ty) (p : Proc A B) BRel s l, simulation (publicRel _) BRel l s p -> (forall x y l, rel BRel l x y -> x = y) -> trace s p.
Proof.
  move=> A B. pcofix CIH.
  intros. move: H1 => Hassum. punfold H0. inv H0.
  de s. de s.
  rewrite /Clause3 in H2. edestruct H2. eauto. simpl. eauto. ssa. pc.
  apply/reduceI_trace; eauto.

  rewrite /Clause4 in H3. edestruct H3. eauto. simpl. eauto. ssa. pc.
  apply/reduceO_trace. eauto. apply Hassum in H4. subst. eauto. eauto.
Qed.

Lemma public_sim2 : forall (A B : Ty) (p : Proc A B) BRel s l,  trace s p -> (forall x y l, rel BRel l x y -> x = y) -> simulation (publicRel _) BRel l s p.
Proof.
  move=> A B + BRel + l. pcofix CIH.
  intros. move: H1 => Hassum. punfold H0. inv H0.
  pfold. econ. done. done. rewrite /Clause3. ssa. inv H2. econ. con. eauto. right.
  apply/CIH. pc. eauto. eauto.
  
  rewrite /Clause4. ssa.
  pfold. econ. done. done. done. rewrite /Clause4. ssa. inv H2. econ. con. eauto.
  econ. con. eauto. right. apply/CIH. pc. eauto. done.
Qed.

Lemma public_NI : forall (A B : Ty) (p : Proc A B) BRel, (forall x y l, rel BRel l x y -> x = y) -> NI _ _ (publicRel _) BRel p.
Proof.
  intros. rewrite /NI. intros. apply/public_sim2;eauto.
Qed.  

Example simple_trace : trace ex3b_stream (bad_scheduler process_pool).
Proof.
  pcofix CIH.
(*  Print bundle.
  Print bundle.
  pfold. rewr. appTrace.
  reduce_once. rewrite /outf. instantiate (1 := inr (Some GetRequest,(None,None))). done.
  reduce_once. reduce_once.
  2: { reduce_once. econ. reduce_once. econ. reduce_once. reduce_once. econ.
  *)     
  bundle. left.  (*1 Get*)
  bundle. left.  (*1 Get*)
  bundle. left.  (*2 Sys*)
  bundle. right. (*5 Notify*)
  swi_instans.
  exact CIH.
Qed.

(*We derive the characterised equivalence classes directly from the input and output type of *)
Definition InputTypeRel : myrel [InputType] := to_rel InputType.
Definition OutputTypeRel : myrel [OutputType] := to_rel OutputType.

Ltac dd H := dependent destruction H.
Example counterexample : NotSim \bot InputTypeRel OutputTypeRel ex3b_stream (bad_scheduler process_pool).
Proof.
Admitted. (*outcomment proof because it is slow*)
(*apply: NS2.
  instantiate (1:= (None,(None,(Some TimerInterrupt)))). (*Input secret timer interrupt*)
  ssa.
  move=>p'. rewr. ssa.
  match_dd.
  apply:NS4.                                             (*Process is expected to output first element of trace in ex3b_stream (myGet),
                                                           but is only able to output Notify.
                                                           This is a contradiction
                                                          *)
  ssa.
  match_dd.
  ssa.
* de H.
* all: try solve [ssa; simpl in H; de H].
Qed.
*)
Example example_not_NI : ~ @NI _ _ InputTypeRel OutputTypeRel (bad_scheduler process_pool).
Proof.
  rewrite /NI. ssa. intro.
  apply/toNotSim. apply/counterexample.
  apply/H. apply simple_trace.
Qed.

(**** Example (b) ****)

(*Definition NI2 I O (p : Proc I O) := NI I O I O p.
Definition f_NI2 {I O :Ty} (f : [I] -> [O]) := forall (l : level) (i i' : [I]) (o o' : [O]), rel I l i i' -> rel O l (f i) (f i').
Definition f_PU2 {I O : Ty} (f : [I] -> [O]) := forall l (i : [I]), dis I l i -> dis O l (f i).
Definition f_NI_PU2 {I O : Ty} (f : [I] -> [O])  := f_NI I O f /\ f_PU I O f.
Definition fv_NI2 (I O V: Ty) (f : [I] -> [V] -> [O]) := forall l (i i' : [I]), rel I l i i' -> forall (v v' : [V]), rel V l v v' -> rel O l (f i v) (f i' v').
Definition f_EP2 (I V: Ty) (f : [I] -> [V] -> [V]) := forall l i, dis I l i -> forall v, rel V l (f i v) v. (*equivalence preserving*)

Lemma out_NI2 : forall I O (o : [O]), NI2 (@out I O o).
Proof. intros. apply: out_NI. Qed.

Lemma map_NI2 : forall (I I' O O' : Ty) (p : Proc I' O) (f : [I] -> [I']) (g : [O] -> [O']),
    f_NI_PU2 f ->
    f_NI2 g ->
    NI2 p ->        
    NI2 (map f g p).
Proof.
  intros. apply/map_NI;eauto.
  all:move: H;rewrite /f_NI_PU2;ssa.
Qed.*)


(*Lemma map_NI3 : forall (Ia Ib Ia' Ib' O O' : Ty) (p : Proc (Times Ia' Ib') O) (f : [Times Ia Ib] -> [Times Ia' Ib']) (g : [O] -> [O']), NI _ _ (eqpair_R Ia Ib) O (@map (Times _ _) (Times _ _) _ _ f g p).*)




(*Lemma iNI_to_LR_boolRel : forall I O (p : Proc (Times Bool I) O) IRel ORel,
    NI (Times Bool I) O (eqpair_LR boolRel IRel) ORel p ->
    NI (Times Bool I) O (eqpair_R boolRel IRel) ORel p.
Proof.
  intros. 
  apply/simulation_I_imp. 3:eauto.
  ssa. de x. de 
Qed.*)

(*Lemma sta_NI2 : forall (I O V : Ty) (p : Proc (Times V I) O) f g v,
    fv_NI2 g->
    fv_NI2 f /\ f_EP2 f ->
    NI _ _ (eqpair_R V I) O p ->    
    NI2 (sta f g v p).
Proof.
  intros. rewrite /NI2.
  ulock. simpl. 
  apply/NI_add_L/NI_add_R.
  apply:sta_NI;eauto.
  (*rewrite /NI2 in H. ssa. apply/NI_I_remove_L. done.*)
  move: H. rewrite /NI2. ssa.
  rewrite /fv_NI;ssa.
Qed.*)

(*We can't use this lemma for example *)
(*Lemma swi_NI2 : forall (I O : Ty) (p : Proc I (Times Bool O)) b,
    NI2 p ->
    oblivious (eqpair_R Bool O) p \bot ->
   (* (forall l, aware Bool true l \/ oblivious (Times Bool O) p l) ->*) (*remove this part, because (to_rel Bool) : myrel [Bool] is always aware*)
    NI2 (swi b p).
Proof.
intros. 
rewrite /NI2. ulock. simpl. 
apply/swi_NI. eauto.
ssa. 
de (eqVneq l \bot). subst. right. move: H0. ulock. ssa.
left. rewrite /aware. ssa. 
Qed.*)

(*Lemma maybe_NI2 : forall (I O :Ty) (p : Proc I O), NI2 p -> NI2 (maybe p).
Proof.
  intros. apply/maybe_NI. eauto.
Qed.

Lemma loop_NI2 : forall (I : Ty) (p : Proc I I), NI2 p -> NI2 (loop p).
Proof.
  intros. apply/loop_NI. ssa.
Qed.

Lemma par_NI2 : forall (I O1 O2 : Ty) (p1 : Proc I O1) (p2 : Proc I O2), NI2 p1 -> NI2 p2 -> NI2 (par p1 p2).
Proof.
  intros. rewrite /NI2. ulock. simpl. apply/NI_add_L/NI_add_R/par_NI;eauto.
  Qed.
*)



(*Mitigator*)
Definition state_type2 := Times (Option Nat) (Times Nat Nat).

Definition inc_state2 (v : [state_type2]) :=
  match v with
  | (None, (0, n)) => (None,(1,n)) (*low/high first step*)
  | (None, (1, 0)) => (Some 0,(0,1)) (*low second step, switch to handler*)
  | (None, (1, 1)) => (Some 0, (0,0)) (*high second step, switch to handler*)                      
  | (Some 0, cn) => (Some 1,cn) (*handler first step*)
  | (Some 1, cn) => (None, cn) (*handler second step, switch to low/high*)
  | _ => v
  end.           
         

Definition to_schedule2 (v : [state_type2]) :=
  match v with
    | (None,cn) => snd cn
    | (Some _, _) => 2
  end.

(*schedules handler between each context switch*)
Definition mitigator := @scheduler state_type2 (fun _ v => v) (fun _ v => inc_state2 v) (None,(0,0)) to_schedule2.
(*Mitigator*)


Ltac rewr ::=  (try rewrite ex3_stream_eq); rewrite /par_swiI /bad_scheduler /process_pool /low_p  /ex3_streamF /bad_scheduler /process_pool /par_swiI3 /high_p /handler /sta_swi /scheduler /mitigator.

Hint Resolve InputTypeRel OutputTypeRel eqsum_LR : rels.

(*Lemma to_rel_eq (A : Ty) l x y  : rel (# A) l x y -> x = y.
Proof. ulock.
  move: A x y. elim;ssa.
  de x. de y. f_equal;eauto.
  de x. de y. f_equal. eauto. de y. f_equal. eauto.
Qed.*)

(*Definition to_rel_eq_IOType := @to_rel_eq IOType.
Definition to_rel_eq_state_type2 := @to_rel_eq state_type2.*)


Lemma eq_to_rel (A : Ty) l x y  : x = y -> rel (# A) l x y.
Proof.
  move=>->. eauto.
Qed.

Definition eq_to_rel_OutputType := @eq_to_rel OutputType.

(*Lemma f_NI_eq A B f: f_NI #A #B f.
  rewrite /f_NI. ssa. apply/eq_to_rel.
  apply to_rel_eq in H. subst. done.
Qed.*)

Lemma f_NI_id (A : Ty) B : @f_NI A A B B id.
  rewrite /f_NI. done.
Qed.

Lemma f_PU_id (A : Ty) B : @f_PU A A B B id.
  rewrite /f_PU. done.
Qed.  
Hint Resolve (*f_NI_eq*) f_NI_id f_PU_id.

(*Lemma mitigator_lem1 : f_NI2 outf.
Proof.
  rewrite /f_NI2 /outf. ssa.
  move/to_rel_eq_IOType: H=>->.
  by apply/eq_to_rel_OutputType.
Qed.
Check f_NI2.
Lemma mitigator_lem2 : @f_NI2 (Times state_type2 IOType) _ (@snd [state_type2] [IOType]).
Proof.
  rewrite /f_NI2. ssa. apply (@to_rel_eq (Times _ _)) in H. subst.
  by apply/(@eq_to_rel IOType).
Qed.  
Hint Resolve mitigator_lem1 mitigator_lem2 : mitdb.*)

(*Ltac clean_rel := repeat match goal with | H : rel (to_rel_locked ?T) _ _ _ |- _  => apply (@to_rel_eq T) in H | |- rel (to_rel_locked ?T) _ _ _ => apply (@eq_to_rel T); subst end.*)

Ltac unify_rels := repeat match goal with
                     | |- NI ?I ?O ?IRel ?ORel _ => first [is_evar IRel; unify IRel (# I)| is_evar ORel; unify ORel (#O)]
                     end.

Ltac NI_apply :=  first [ apply: map_NI | apply:sta_NI | apply:swi_NI | apply:loop_NI | apply:out_NI (*apply:map_NI2 | apply:loop_NI2 | apply:sta_NI2 | apply:par_NI2 | apply:maybe_NI2 | apply:out_NI2*) ].
Ltac NI_post := ssa;rewrite /outf /fv_NI /f_PU /f_NI /par_swiI3 /process_pool;ssa;(*clean_rel;*)
               try solve [ intros;(*clean_rel;*)ssa | eauto with mitdb].
Ltac NI_tac := NI_apply;NI_post.
Lemma dis_pair : forall A B l a b, dis (Times A B) l (a,b) -> dis A l a.
Proof.
  ssa. move: H. ulock. ssa.
Qed.

Lemma dis_pair' : forall (A B : Ty) l a b, dis A l a -> dis B l b -> dis (Times A B) l (a,b).
Proof.
  ssa. 
Qed.
Lemma level_leq : forall (l : level), l <= l.
Proof. done.
Qed.

Hint Resolve level_leq.

Lemma dis_inl : forall A B l a, dis (# (Sum A B)) l (inl a) -> dis A l a.
Proof.
  ssa.
Qed.

Lemma dis_inr : forall A B l b, dis (# (Sum A B)) l (inr b) -> dis B l b.
Proof.
  ssa.
Qed.

(*swi_NI shows (swi b p) is NI (eqpair_LR VRel IRel) ORel
  Sometimes we need the stronger property (eqpair_R VRel IRel), or do we?? *)
Lemma swi_NI'
     : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (p : Proc I (Times Bool O)) (b : bool),
       NI I (Times Bool O) IRel (eqpair_LR (privateRel Bool) ORel) p ->
       (forall l : Order.TBLattice.sort level, aware (privateRel Bool) true l \/ oblivious (eqpair_R (privateRel Bool) ORel) p l) ->
       NI (Times Bool I) (Option O) (eqpair_R (privateRel Bool) IRel) (eqmaybe ORel) (swi b p).
Proof.
  intros.
  apply/NI_I_imp. 3: { apply/swi_NI. eauto. eauto. }
                ssa. ssa.
  de H1.
Qed.

Definition InputRel3 := eqmaybe_false (semiprivateRel TInterrupt).
Definition InputRel2 := eqpair_LR (eqmaybe_false (semiprivateRel THandlerOutput)) InputRel3.
Definition InputRel : myrel [InputType] := eqpair_LR (eqmaybe_false (publicRel Unit)) InputRel2.

Definition OutputRel : myrel [OutputType] := eqpair_LR (eqmaybe_false (publicRel TPublicOutput))
                                               (eqpair_LR (eqmaybe_false (semiprivateRel TTypeSyscall)) (eqmaybe_false (semiprivateRel THandlerOutput))).

Ltac mrw := rewrite /f_NI /f_PU /fv_NI /f_EP.

Check f_NI.

(*Lemma f_NI_inl : forall (A B : Ty) ARel BRel, f_NI (eqpair ARel BRel) ARel inl.*)

Lemma rel_eqpair : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, rel (eqpair ARel BRel) l a b -> rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2.
Proof.
  ssa.
Qed.

Lemma rel_eqpair2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, 
    rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2 -> rel (eqpair ARel BRel) l a b.
Proof.
  ssa.
Qed.

(*Lemma rel_eqpair_L : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, rel (eqpair_L ARel BRel) l a b -> rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2.
Proof.
  ssa. de H. de H.
Qed.

Lemma rel_eqpair_R : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, rel (eqpair_R ARel BRel) l a b -> rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2.
Proof.
  ssa.
Qed.*)

Lemma rel_eqpair_R2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a1 a2 b1 b2,  rel ARel l a1 a2 /\ rel BRel l b1 b2 \/ dis BRel l b1 /\ dis BRel l b2 -> rel (eqpair_R ARel BRel) l (a1,b1) (a2,b2).
Proof.
  ssa.
Qed.

Lemma rel_eqpair_R2' : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a1 a2 b1 b2, rel (eqpair_R ARel BRel) l (a1,a2) (b1,b2) -> rel ARel l a1 b1 /\ rel BRel l a2 b2  \/ dis BRel l a2 /\ dis BRel l b2.
Proof.
  ssa.
Qed.

Lemma rel_eqpair_L2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a1 a2 b1 b2,  rel ARel l a1 a2 /\ rel BRel l b1 b2 \/ dis ARel l a1 /\ dis ARel l a2 -> rel (eqpair_L ARel BRel) l (a1,b1) (a2,b2).
Proof.
  ssa.
Qed.

Lemma rel_eqpair_L2' : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a1 a2 b1 b2, rel (eqpair_L ARel BRel) l (a1,b1) (a2,b2) -> rel ARel l a1 a2 /\ rel BRel l b1 b2  \/ dis ARel l a1 /\ dis ARel l a2.
Proof.
  ssa.
Qed.

Lemma rel_eqpair_LR : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, rel (eqpair_LR ARel BRel) l a b -> rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2.
Proof.
  ssa.
Qed.

Lemma rel_eqpair_LR2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a1 a2 b1 b2,  rel ARel l a1 b1 /\ rel BRel l a2 b2 -> rel (eqpair_LR ARel BRel) l (a1,a2) (b1,b2).
Proof.
  ssa.
Qed.

(*Lemma rel_eqpair_OR : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, rel (eqpair_OR ARel BRel) l a b -> rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2.
Proof.
  ssa. de H. de H. de H0.
Qed.*)

Lemma dis_eqpair_R : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, dis (eqpair_R ARel BRel) l (a,b) -> dis BRel l b.
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_R2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, dis BRel l b -> dis (eqpair_R ARel BRel) l (a,b).
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_L : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, dis (eqpair_L ARel BRel) l (a,b) -> dis ARel l a.
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_L2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, dis ARel l a -> dis (eqpair_L ARel BRel) l (a,b).
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_LR : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, dis (eqpair_LR ARel BRel) l (a,b) -> dis ARel l a /\ dis BRel l b.
Proof.  
  intros. ssa.
Qed.

Lemma dis_eqpair_LR2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, dis ARel l a /\ dis BRel l b -> dis (eqpair_LR ARel BRel) l (a,b).
Proof.  
  intros. ssa.
  Qed.


Lemma f_NI_snd_eqpair : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]), f_NI (eqpair ARel BRel) BRel snd. 
Proof.
mrw. ssa.
Qed.

(*Lemma f_NI_snd_eqpair_L : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]), f_NI (eqpair_L ARel BRel) BRel snd. 
Proof.
mrw. ssa. de H.
Qed.

Lemma f_NI_snd_eqpair_R : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]), f_NI (eqpair_R ARel BRel) BRel snd. 
Proof.
mrw. ssa.
Qed.*)

Lemma f_NI_snd_eqpair_LR : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]), f_NI (eqpair_LR ARel BRel) BRel snd. 
Proof.
mrw. ssa.
Qed.

(*Lemma f_NI_snd_eqpair_OR : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]), f_NI (eqpair_OR ARel BRel) BRel snd. 
Proof.
mrw. ssa. de H. de H. de H0.
Qed.*)

Hint Resolve f_NI_snd_eqpair (*f_NI_snd_eqpair_L f_NI_snd_eqpair_R*) f_NI_snd_eqpair_LR (*f_NI_snd_eqpair_OR*) : tempdb.

Lemma rel_eqsum_LR : forall (A B : Ty) (a1 a2 : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel ARel l a1 a2 -> rel (eqsum_LR ARel BRel) l (inl a1) (inl a2). 
Proof. ssa.
Qed.

Lemma rel_eqsum_LR2 : forall (A B : Ty) (b1 b2 : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel BRel l b1 b2 -> rel (eqsum_LR ARel BRel) l (inr b1) (inr b2). 
Proof. ssa.
Qed.

Lemma rel_eqsum_LR' : forall (A B : Ty) (a1 a2 : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l,rel (eqsum_LR ARel BRel) l (inl a1) (inl a2) ->  rel ARel l a1 a2. 
Proof. ssa.
Qed.

Lemma rel_eqsum_LR2' : forall (A B : Ty) (b1 b2 : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel (eqsum_LR ARel BRel) l (inr b1) (inr b2) -> rel BRel l b1 b2. 
Proof. ssa.
Qed.

Lemma dis_eqsum_LR : forall (A B : Ty) (a : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l, dis ARel l a -> dis (eqsum_LR ARel BRel) l (inl a). 
Proof. ssa.
Qed.

Lemma dis_eqsum_LR' : forall (A B : Ty) (a : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l,  dis (eqsum_LR ARel BRel) l (inl a) -> dis ARel l a. 
Proof. ssa.
Qed.

Lemma rel_eqsum : forall (A B : Ty) (a1 a2 : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel ARel l a1 a2 -> rel (eqsum ARel BRel) l (inl a1) (inl a2). 
Proof. ssa.
Qed.

Lemma rel_eqsum2 : forall (A B : Ty) (b1 b2 : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel BRel l b1 b2 -> rel (eqsum ARel BRel) l (inr b1) (inr b2). 
Proof. ssa.
Qed.

Lemma rel_eqsum' : forall (A B : Ty) (a1 a2 : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l,rel (eqsum ARel BRel) l (inl a1) (inl a2) ->  rel ARel l a1 a2. 
Proof. ssa.
Qed.

Lemma rel_eqsum2' : forall (A B : Ty) (b1 b2 : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel (eqsum ARel BRel) l (inr b1) (inr b2) -> rel BRel l b1 b2. 
Proof. ssa.
Qed.

Lemma rel_eqsum_L : forall (A B : Ty) (a1 a2 : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel ARel l a1 a2 -> rel (eqsum_L ARel BRel) l (inl a1) (inl a2). 
Proof. ssa.
Qed.

Lemma rel_eqsum_L2 : forall (A B : Ty) (b1 b2 : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel BRel l b1 b2 -> rel (eqsum_L ARel BRel) l (inr b1) (inr b2). 
Proof. ssa.
Qed.

Lemma rel_eqsum_L' : forall (A B : Ty) (a1 a2 : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l,rel (eqsum_L ARel BRel) l (inl a1) (inl a2) ->  rel ARel l a1 a2. 
Proof. ssa.
Qed.

Lemma rel_eqsum_L2' : forall (A B : Ty) (b1 b2 : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel (eqsum_L ARel BRel) l (inr b1) (inr b2) -> rel BRel l b1 b2. 
Proof. ssa.
Qed.

Lemma dis_eqsum_L : forall (A B : Ty) (a : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l, dis ARel l a -> dis (eqsum_L ARel BRel) l (inl a). 
Proof. ssa.
Qed.

Lemma dis_eqsum_L2 : forall (A B : Ty) (a : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l, dis (eqsum_L ARel BRel) l (inl a) -> dis ARel l a. 
Proof. ssa.
Qed.

Lemma rel_eqsum_R : forall (A B : Ty) (a1 a2 : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel ARel l a1 a2 -> rel (eqsum_R ARel BRel) l (inl a1) (inl a2). 
Proof. ssa.
Qed.

Lemma rel_eqsum_R2 : forall (A B : Ty) (b1 b2 : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel BRel l b1 b2 -> rel (eqsum_R ARel BRel) l (inr b1) (inr b2). 
Proof. ssa.
Qed.

Lemma rel_eqsum_R' : forall (A B : Ty) (a1 a2 : [A]) (ARel : myrel [A]) (BRel : myrel [B]) l,rel (eqsum_R ARel BRel) l (inl a1) (inl a2) ->  rel ARel l a1 a2. 
Proof. ssa.
Qed.

Lemma rel_eqsum_R2' : forall (A B : Ty) (b1 b2 : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, rel (eqsum_R ARel BRel) l (inr b1) (inr b2) -> rel BRel l b1 b2. 
Proof. ssa.
Qed.

Lemma dis_eqsum_R : forall (A B : Ty) (b : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, dis BRel l b -> dis (eqsum_R ARel BRel) l (inr b). 
Proof. ssa.
Qed.

Lemma dis_eqsum_R2 : forall (A B : Ty) (b : [B]) (ARel : myrel [A]) (BRel : myrel [B]) l, dis (eqsum_R ARel BRel) l (inr b) -> dis BRel l b. 
Proof. ssa.
Qed.


(*Example dis_test : dis InputRel \bot (None, (None, Some DiskInterrupt)).
ssa. 
Defined.*)


Definition streamTypeb := Stream ([InputType] + [OutputType]). 
Definition newtraceFb (s : streamTypeb) := Cons (inr (Some GetRequest,(None,None)))
                                             (Cons (inr (Some GetRequest, (None,None)))
                                             (Cons (inr (None, (None, Some Nothing)))
                                             (Cons (inr (None, (None, Some Nothing)))
                                             (Cons (inr (None,(Some Syscall, None)))
                                                (Cons (inr (None, (Some Syscall, None)))
                                                   (Cons (inr (None, (None, Some Nothing)))
                                                      (Cons (inr (None, (None, Some Nothing))) s))))))). 
CoFixpoint newtraceb := newtraceFb newtraceb.                                             

Lemma newtraceb_eq : newtraceb = newtraceFb newtraceb.
Proof.
rewrite {1}/newtraceb.
rewrite {1}(coseq_match (cofix newtrace : streamTypeb := newtraceFb newtrace)).
simpl.
rewrite /newtraceFb.
do ? f_equal.
Qed.

(*Trace derivation*)
Ltac rewr ::=  (try rewrite newtraceb_eq); rewrite /mitigator /par_swiI3 /sta_swi /low_p /newtraceFb /process_pool /par_swiI /scheduler /handler /high_p /alternate_generic.

Lemma newtraceb_trace : trace newtraceb (mitigator process_pool).
Proof.
  pcofix CIH.
  rewr.
  do 7 try (bundle;left).

  bundle. right. 
  swi_instans. eauto.
Qed.

(*counterexample no longer derivable*)
(*Lemma counterexampleb : NotSim \bot InputRel OutputRel newtraceb (mitigator process_pool).
Proof.
  rewr.
  apply/NS4.
  intros. match_dd. ssa.
  apply/NS4.
  intros. match_dd;ssa.
  apply/NS2. apply/dis_test.
  intros. match_dd.
  apply/NS4. intros. match_dd;ssa.
Qed.*)



(*Ltac instantiate_eqsum_LR := match goal with
                          | |- f_NI ?IRel (?ORel : ?T) inl => evar (e : T) ; idtac "hello";unify ORel (@eqsum_LR _ _ IRel e)
                          | |- f_NI ?IRel ?ORel inr => unify ORel (@eqsum_LR I O  _ ORel);shelve                                                 end.*)
Lemma rel_eqpair_to_L : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l x y, rel (eqpair ARel BRel) l x y -> rel (eqpair_L ARel BRel) l x y.
Proof.
  ssa.
Qed.

Lemma simp_pair1 : forall (A B: Type) (a : A) (b : B), (a,b).1 = a.
Proof. done.
Qed.
Lemma simp_pair2 : forall (A B: Type) (a : A) (b : B), (a,b).2 = b.
Proof. done.
Qed.

Lemma rel_eqmaybe : forall (A : Ty) (ARel : myrel [A]) l x y, rel ARel l x y -> rel (eqmaybe ARel) l (Some x) (Some y).
Proof. ssa.
Qed.
       
Definition pair_rewr := (simp_pair1,simp_pair2).

(*
Theorem mitigator_NI : NI _ _ InputRel OutputRel (mitigator process_pool).
 *)
(*mitigator process_pool does not work so I will work on new example from now on*)
Print high_p.
Definition Input' := Sum TPublicInput (Sum THandlerOutput TInterrupt).
(*Definition Inter := Sum TPublicInput (Sum THandlerOutput Unit).*)
Definition Output' := Times (Option TPublicOutput) (Times (Option TTypeSyscall) (Option THandlerOutput)).

Definition InputRel' : myrel [Input'] := eqsum_LR (publicRel _) (eqsum_LR (semiprivateRel _ ) (semiprivateRel _)).
(*Definition InterRel : myrel [Inter] := eqsum_R (publicRel _) (semiprivateRel _).*)
Definition OutputRel' : myrel [Output'] := eqpair_LR (publicRel _) (*also consider eqmaybe publicRel*)
                           (eqpair_LR (semiprivateRel _) (semiprivateRel _)).

Definition inl_some {A B : Set} (x : A + B) := if x is inl x' then Some x' else None.
Definition inr_some {A B : Set} (x : A + B) := if x is inr x' then Some x' else None.
Definition option_inl_some {A B : Set} (x : option (A + B)) := if x is Some (inl x') then Some x' else None.


Definition inr_inl_some {A B C : Set} (x : A + (B + C)) := if x is inr (inl x') then Some x' else None.
Definition inr_inr_some {A B C : Set} (x : A + (B + C)) := if x is inr (inr x') then Some x' else None.

Definition is_none (A : Set) (x : option A) := if x is None then true else false.
Definition is_some (A : Set) (x : option A) := if x is Some _ then true else false.
Definition some_inl (A B : Set) (x : option (A + B)) : option A := if x is Some (inl x') then Some x' else None.

(*the new goal is to make par_swi_N*)
(*idea is that par_swi p0 p1 : proc V V and p0,p1 : proc V V.
 This works for input but for output we get par_swi p0 p1 : proc V (V*V)
 *)
(*f 0 i = initial configuration for i
  f 1 i = delta to reached desired next configuration*)
Fixpoint sum_N n (f : nat -> Ty) : Ty :=
  let t := f n in
  match n with
  | 0 => t
  | S n' => Sum t (sum_N n' f)
  end.

Fixpoint times_N n (f : nat -> Ty) : Ty :=
  let t := f n in
  match n with
  | 0 => t
  | S n' => Times t (times_N n' f)
  end.

Definition map_option (A B : Set) (f : A -> B) (x : option A) : option B := if x is Some x' then Some (f x') else None.
Definition map_sum {A B C D :Set} (f : A -> C) (g : B -> D) := fun (x: A + B) => match x with
                                                                                | inl x' => inl (f x')
                                                                                | inr x' => inr (g x')
                                                                                 end.
Definition map_pair {A B C D :Set} (f : A -> C) (g : B -> D) := fun (x: A * B) => match x with
                                                                                | (x0,x1) => (f x0, g x1)
                                                                                  end.
Definition Input_n (n : nat) (f_I : nat -> Ty) := sum_N n f_I.
Definition Output_n (n : nat) (f_O : nat -> Ty) := times_N n (Option \o f_O).

Definition scheduled_process_pool
  (n : nat)
  (f_I f_O : nat -> Ty)
  (f_sch : nat -> forall n, [Option (f_I n)] -> bool)
  (f_proc : forall n, Proc (f_I n) (f_O n)) : Proc (Times Nat (Option (Input_n n f_I))) (Output_n n f_O).
  elim: n.
  - simpl.
    eapply map.
      instantiate (1:= Times Bool (Option (f_I 0))). exact (fun n => ((@f_sch (fst n) 0 (snd n) ,snd n))).
      exact id. 
    eapply swi. exact (@f_sch 1 0 None).
    eapply maybe. 
    eapply map.
      eapply id. 
      exact (fun o => (false,o)).
    exact (f_proc 0).

  - intros. simpl.
    eapply par.
    * eapply map.
      instantiate (1:= Times Bool (Option (f_I n.+1))).
      exact (fun x => ((@f_sch (fst x) (n.+1) (some_inl (snd x))), option_inl_some (snd x))).
        exact id. 
      eapply swi.
        exact (@f_sch 1 n.+1 None). 
      eapply maybe.
      eapply map.
        exact id.     
        exact (fun o => (false,o)).
      (*eapply maybe.*) (*not necessary anymore*)
      exact (f_proc n.+1).
    * eapply map. 3: apply H.
        exact (map_pair id (fun x => match x with | Some (inl _) => None | Some (inr x') => Some x' | None => None end )).
        exact id. 
Defined.


(*original process pool definition with two maybes because we discard input with first maybe by schedule without message and second maybe with projection of some type*)
(*Definition scheduled_process_pool
  (n : nat)
  (f_I f_O : nat -> Ty)
  (f_sch : nat -> forall n, [Option (f_I n)] -> bool)
  (f_proc : forall n, Proc (f_I n) (f_O n)) : Proc (Times Nat (Option (Input_n n f_I))) (Output_n n f_O).
  elim: n.
  - simpl.
    eapply map.
      instantiate (1:= Times Bool (Option (f_I 0))). exact (fun n => ((@f_sch (fst n) 0 (snd n) ,snd n))).
      exact id. 
    eapply swi. exact (@f_sch 1 0 None).
    eapply maybe. 
    eapply map.
      eapply id. 
      exact (fun o => (false,o)).
    exact (f_proc 0).

  - intros. simpl.
    eapply par.
    * eapply map.
        instantiate (1:= Times Bool (Option (Sum (f_I n.+1) (sum_N n f_I)))). exact (fun x => ((@f_sch (fst x) (n.+1) (some_inl (snd x))),snd x)).
        exact id. 
      eapply swi.
        exact (@f_sch 1 n.+1 None).
      eapply maybe.
      eapply map.
        instantiate (1:= Option (f_I n.+1)). exact inl_some. (*sum mapping*)
        exact (fun o => (false,o)).
      eapply maybe.
      exact (f_proc n.+1).
    * eapply map. 3: apply H.
        exact (map_pair id (fun x => match x with | Some (inl _) => None | Some (inr x') => Some x' | None => None end )).
        exact id. 
Defined.*)

Definition alternate_generic2 (A B : Ty) (x y : [B]) (pred : [A] -> bool) :=
  @map _ (Sum _ _) (Sum _ (Times Bool Unit)) B 
                        inl
                        (fun o => if o is inr (true,tt) then x else y)
                        (@loop (Sum A (Times Bool Unit))
                        (@map (Sum A _) _ _ (Sum _ _) id (fun o => inr o)
                        ((@sta (Sum _ _) _ Bool
                           (fun i v => match i with | inl i' => v || pred i' | _ => false end)
                           (fun o v => v)
                           false
                           (@out (Times Bool _ ) Unit tt)
                        )))).
Definition high_p2 := @alternate_generic2 THandlerOutput TTypeSyscall Syscall NOP (fun i => i == Notify).


Definition my_f_I := fun (n : nat) => match n with
                                      | 0 => TInterrupt
                                      | 1 => THandlerOutput
                                      | _ => Unit
                                      end.
Definition my_f_O := fun (n : nat) => match n with
                                      | 0 => THandlerOutput
                                      | 1 => TTypeSyscall
                                      | 2 => TPublicOutput
                                      | _ => Unit
                                      end.

(*Definition my_f_sch (f_I : nat -> Ty) : nat -> forall n, [Option (f_I n)] -> bool :=
  fun nt np _ => let nt' := if nt < 2 then nt else (nt%%8)+1 in
  match nt',np with
  | 1,2 | 2,2 => true 

  | 3,0 | 4,0 => true

  | 5,1 | 6,1 => true

  | 7,0 | 8,0 => true

  | 9,0 => true
  | 9,2 => true           
  | _,_ => false
  end.*)

Definition my_f_sch (f_I : nat -> Ty) : nat -> forall n, [Option (f_I n)] -> bool :=
  fun nt np _ => 
  match nt%%8,np with
  | 1,0 => nt != 1
  | 1,2 => true 

  | 3,2 => true           
  | 3,0 => true

  | 5,0 => true
  | 5,1 => true

  | 7,1 => true
  | 7,0 => true
  | _,_ => false
  end.

Definition unit_p : Proc Unit Unit := @out Unit Unit tt.

Definition my_procs : forall n, Proc (my_f_I n) (my_f_O n).
  case. apply handler.
  case. apply high_p2.
  case. apply low_p.
  elim. apply unit_p.
  intros. apply unit_p.
Defined.

Definition process_pool3 := @scheduled_process_pool 2 my_f_I my_f_O (@my_f_sch my_f_I) my_procs.

Definition LoopType_n (n : nat) (f_I f_O : nat -> Ty) := Sum (Input_n n f_I) (Output_n n f_O).

Definition None_N (n : nat) (f_O : nat -> Ty) : [(Output_n n f_O)].
elim: n. simpl. exact None.
intros. simpl. eapply pair. exact None. exact H.
Defined.

Definition collapse_in_out (n : nat) (f_I f_O : nat -> Ty) (x : [LoopType_n n f_I f_O]) : [Output_n n f_O]  :=
  match x with
  | inl _ => None_N n f_O
  | inr x' => x'
  end.
(*(LoopType_n n f_I f_O)*)

Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.

(*Definition mitigator3
  (T_in T_in' T_out T_out' : Ty)   
  (f_in : [T_in] -> [T_in'])
  (f_out : [T_out'] -> [T_out])
  (f_route : [T_out'] -> [Option T_in'])
  (def : [T_out'])
  (p : Proc (Times Nat (Option T_in')) T_out')
  : Proc T_in T_out :=
  @map T_in T_in' T_out' T_out f_in f_out
  (@map T_in' (Sum T_in' T_out') (Sum T_in' T_out') T_out' inl (inr_or_def def)
                          (@loop (Sum T_in' T_out')
                             (@map _ _ (Times _ _) _
                                id snd
                                (@sta _ _ Nat (fun i v => v) (fun o v => (v+1)%%8) 1
                                   (@map (Times Nat (Sum T_in' T_out'))
                                      (Times Nat (Option T_in'))
                                _ (Sum _ _)
                                (fun i  =>
                                   match snd i with
                                   | inl i' => ((0,Some i'))
                                   | inr o  => map_pair id f_route (fst i,o)
                                   end) inr
                                p))))).*)

Definition loop_and_count
  (n_state : nat)           
  (T_in' T_out' : Ty)   
  (f_route : [T_out'] -> [Option T_in'])
  (def : [T_out'])
  (p : Proc (Times Nat (Option T_in')) T_out')
  : Proc T_in' T_out' :=
  (@map T_in' (Sum T_in' T_out') (Sum T_in' T_out') T_out' inl (inr_or_def def)
                          (@loop (Sum T_in' T_out')
                             (@map _ _ (Times _ _) _
                                id snd
                                (@sta _ _ Nat (fun i v => v) (fun o v => (v+1)) n_state
                                   (@map (Times Nat (Sum T_in' T_out'))
                                      (Times Nat (Option T_in'))
                                _ (Sum _ _)
                                (fun i  =>
                                   match snd i with
                                   | inl i' => ((0,Some i'))
                                   | inr o  => map_pair id f_route (fst i,o)
                                   end) inr
                                p))))).

Definition my_T_in := Sum Unit TInterrupt.
Definition my_T_out := Option (Option (Sum TPublicOutput TTypeSyscall)).

Definition my_T_in' := Input_n 2 my_f_I.
Definition my_T_out' := Output_n 2 my_f_O.

Definition my_f_in (t : [my_T_in]) : [my_T_in'] := match t with | inl tt => inl tt | inr t => inr (inr t) end.
Definition my_f_out (t : [my_T_out']) := match t with
                                         | (Some p,(None,None)) => Some (Some (inl p))
                                         | (None,(Some h,None)) => Some (Some (inr h))
                                         | (None,(None,Some h)) => Some None
                                         | _ => None                               
                                         end.

  Definition f_out_dis (v : [my_T_out]) := match v with | Some (Some (inl _)) | None => False | Some (Some (inr _)) | Some None  => True end.
  Definition my_f_out_rel : myrel ([my_T_out]).
  refine (@MyRel _
            (fun l (v : [my_T_out]) => l = \bot /\ f_out_dis v )
            (fun l v1 v2 => v1 = v2 \/ f_out_dis v1 /\ f_out_dis v2)
            _
            _
            _
            _).
  intros. con. intro. auto. intro. intros. de H.
  intro. intros. de H. de H0. left. subst. auto. subst. eauto.
  de H0. subst. eauto.
  intros. de H0.
  intros. ssa. subst. apply order_bot in H. done.
  intros. ssa. subst. con. case. intros. eauto.
  case. intros. subst. eauto.
  ssa.
  Defined.
  
(*Definition my_f_out (t : [my_T_out']) := match t with
                                              |(Some publ,(None,None)) => Some (inl publ)
                                              |(None,(Some prv,None)) => Some (inr prv)
                                              |_ => None
                                           end.*)

Definition my_f_route (t : [my_T_out']) : [Option my_T_in'] :=
  match t with
  | (_,(_,(Some h))) => Some (inr (inl h))
  | _ => None
  end.

Definition my_def := None_N 2 my_f_O.



(*Definition my_mitigator3 := @mitigator3 my_T_in my_T_in' my_T_out my_T_out' my_f_in my_f_out my_f_route my_def.*)
Definition my_loop_and_count := @loop_and_count 1 my_T_in' my_T_out' my_f_route my_def.

(*
(*small detail, we need to allow interrupt to pass through even though p1 is scheduled, otherwise we block the handler*)
Definition steps_to_proc (n : nat) := (*if n < 2 then n else if n < 4 then 2 + n else n - 2.*)
  match n with
  | 0 => 1
  | 2 => 1
  | 4 => 0
  | 6 => 0
  | _ => 0
  end.         

 *)

Definition no_input (s : Stream (Interrupt + option (PublicOutput + TypeSyscall))) :=
  Cons (inr (Some (inl GetRequest)))
 (Cons (inr (Some (inl GetRequest)))
 (Cons (inr (Some (inr NOP)))
 (Cons (inr (Some (inr NOP)))
    s))).

Definition bad_schedule (s : Stream (Interrupt + option (PublicOutput + TypeSyscall))) :=
  Cons (inr (Some (inl GetRequest)))
 (Cons (inl DiskInterrupt)
 (Cons (inr None)
 (Cons (inr (Some (inl GetRequest)))
 (Cons (inr (Some (inr Syscall)))
 (Cons (inr (Some (inr NOP)))
    s))))).


Definition good_schedule (s : Stream (Interrupt + option (PublicOutput + TypeSyscall))) :=
  Cons (inr (Some (inl GetRequest)))
 (Cons (inl DiskInterrupt)
 (Cons (inr (Some (inl GetRequest)))
 (Cons (inr None)          
 (Cons (inr (Some (inr Syscall)))
 (Cons (inr (Some (inr NOP)))
  s))))).


Definition wrap_trace s :=
                                          Cons (inl (DiskInterrupt)) (*input*)
                                          (Cons (inr (Some (inl GetRequest))) (*public out*)
                                          (Cons (inr (Some (inl GetRequest))) (*public out*)
                                            (Cons (inr None)(*InternalStep*)
                                            (Cons (inr None)(*InternalStep*)
                                              (Cons (inr (Some (inr Syscall))) (*private out*)
                                              (Cons (inr (Some (inr NOP))) (*private out*)
                                                (Cons (inr None)(*InternalStep*)
                                                (Cons (inr None)(*InternalStep*)                                                 
                                                  s)))))))).


(*We include state change for public process to show that it cannot receive input when it is not scheduled. If we try to consume the output trace that assumes that input has been received then we fail*)
Definition streamTypec := Stream ([my_T_in'] + [my_T_out']).

Definition out1 x : [my_T_out'] := (Some x,(None,None)).
Definition out2 x : [my_T_out'] := (None,(Some x,None)).
Definition out3 x : [my_T_out'] := (None,(None,Some x)).

Definition newtraceFc (s : streamTypec) :=
                                          Cons (inl (inr (inr DiskInterrupt)))
                                          (Cons (inr (out1 GetRequest))(*public*)
                                          (Cons (inr (out1 GetRequest))(*public*)
                                            (Cons (inr (out3 Notify))(*handler*)
                                            (Cons (inr (out3 Nothing))(*handler*)
                                              (Cons (inr (out2 Syscall)) (*private*)
                                              (Cons (inr (out2 NOP)) (*private*)
                                                (Cons (inr (out3 Nothing))(*handler*)
                                                (Cons (inr (out3 Nothing))(*handler*)                                                 
                                                  s)))))))).

CoFixpoint newtracec := newtraceFc newtracec.                                             

Lemma newtracec_eq : newtracec = newtraceFc newtracec.
Proof.
rewrite {1}/newtracec.
rewrite {1}(coseq_match (cofix newtrace : streamTypec := newtraceFc newtrace)).
simpl.
rewrite /newtraceFc.
do ? f_equal.
Qed.

(*Trace derivation*)
Ltac rewr ::=  (try rewrite newtracec_eq); rewrite /mitigator /par_swiI3 /sta_swi /low_p /newtraceFb /process_pool /par_swiI /scheduler /handler /high_p (*/my_mitigator3*) /loop_and_count /my_loop_and_count (*/mitigator3*) /process_pool3 /scheduled_process_pool /high_p2 /alternate_generic /alternate_generic2 /low_p /loop_and_count.




(*Need a stronger coinduction hypothesis which makes reasoning on state natural number becomes symbolic, so then extra theorems must be shown. We skip this for now*)
Lemma newtracec_trace : trace newtracec (my_loop_and_count process_pool3).
Proof.
  pcofix CIH.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left. 
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;right.  
  swi_instans.
  have: 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 1. admit.
  move=>->. eauto.
Admitted.
Check rel_eqmaybe.
(*Lemma rel_eqmaybe : forall (A : Ty) (ARel : myrel [A]) x y l, rel ARel l x y -> rel (eqmaybe ARel) l (Some x) (Some y).*)

  Ltac inner_match H := match H with
                         | context[match ?x with _ => _ end] => first [ inner_match x | idtac x;de x ]
                         end.                                             

  Ltac temp_tac := (match reverse goal with
                           | H : _ \/ _ |- _ => de H
                           | H : match ?x with _ => _ end |- _ => de x
                           | |- ?H => inner_match H
                    end                      
                    ;subst;ssa).

  Lemma rel_eqpair_OR : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l x0 x1 y0 y1,
      rel (eqpair_OR ARel BRel) l (x0,x1) (y0,y1) -> rel ARel l x0 y0 /\ rel BRel l x1 y1 \/ (dis ARel l x0 \/ dis BRel l x1) /\ (dis ARel l y0 \/ dis BRel l y1).  
  Proof. ssa.
  Qed.

  
  Lemma level_not : forall (l : level), ~ (l <> \bot) -> l = \bot.
    intros. de (eqVneq l \bot). exfalso. apply H. intro. subst. by rewrite eqxx in i.
  Qed.
  Hint Resolve level_not.

  Lemma rel_eqmaybe_top_aux : forall (A : Ty) (ARel : myrel [A]) l x y, rel (eqmaybe_top ARel) l x y -> match x,y with
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

  Lemma rel_eqmaybe_top : forall (A : Ty) (ARel : myrel [A]) l x y, rel (eqmaybe_top ARel) l x y -> (exists x' y', x = Some x' /\ y = Some y' /\ rel ARel l x' y') \/
                                                                                                      (exists x', x = Some x' /\ y = None /\ l = \bot /\ dis ARel l x') \/
                                                                                                      (exists y', x = None /\ y = Some y' /\ l = \bot /\ dis ARel l y') \/ x = None /\ y = None.
  Proof.
    intros. de x. de y. left. eauto.
    right. left. econ.  eauto.
    de y. right. right. econ. econ. eauto.
  Qed.

  Lemma rel_eqmaybe_top2 : forall (A : Ty) (ARel : myrel [A]) l x y, rel ARel l x y -> rel (eqmaybe_top ARel) l (Some x) (Some y).
    Proof. ssa.
    Qed.

  Lemma rel_eqmaybe_false2 : forall (A : Ty) (ARel : myrel [A]) l x y, rel ARel l x y -> rel (eqmaybe_false ARel) l (Some x) (Some y).
    Proof. ssa.
    Qed.

    
  Lemma rel_eqmaybe_aux : forall (A : Ty) (ARel : myrel [A]) l x y, rel (eqmaybe ARel) l x y -> match x,y with
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

  Lemma rel_eqmaybe2 : forall (A : Ty) (ARel : myrel [A]) l x y, rel (eqmaybe ARel) l x y -> (exists x' y', x = Some x' /\ y = Some y' /\ rel ARel l x' y') \/
                                                                                               x = None /\ y = None.
  Proof.
    intros.
    de x. de y.
    left. eauto.
    de y.
  Qed.

  Lemma dis_eqmaybe : forall (A : Ty) (ARel : myrel [A]) l v, dis (eqmaybe ARel) l v -> exists v', v = Some v' /\ dis ARel l v'.
  Proof.
    intros. ssa. de v. econ. eauto.
  Qed.

  Lemma dis_eqmaybe2 : forall (A : Ty) (ARel : myrel [A]) l x, dis ARel l x -> dis (eqmaybe ARel) l (Some x). 
  Proof.
    intros. ssa. 
  Qed.

  Lemma dis_eqmaybe_false2 : forall (A : Ty) (ARel : myrel [A]) l x, dis ARel l x -> dis (eqmaybe_false ARel) l (Some x). 
  Proof.
    intros. ssa. 
  Qed.    

  Definition intermediate_outputRel := eqpair ((eqmaybe (publicRel TPublicOutput))) (eqpair (eqmaybe (semiprivateRel (TTypeSyscall))) (eqmaybe (semiprivateRel (THandlerOutput)))).


  Definition is_inl (A B : Set) (x : A + B) := if x is inl _ then true else false.
  Definition is_inr (A B : Set) (x : A + B) := if x is inr _ then true else false.

  Lemma dis_eqsum_LR2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l b, dis BRel l b -> dis (eqsum_LR ARel BRel) l (inr b).
  Proof. intros. ssa.
  Qed.

(*  Lemma test_test : forall (ARel : myrel [Bool]) l, (forall l x, dis ARel l x = true \/ dis ARel l x = false) ->  aware ARel true l -> aware ARel false l.
    rewrite /aware. intros.
    destruct v'.
    have: rel ARel l true false. auto.
    move/H0. ssa.
    ssa.
    intro.
    move: (H l true).
    intros. destruct H3.
    have: rel ARel l true false. destruct ARel. ssa.
    apply/i. rewrite H3. done. done.
    move/H0. ssa.
*)    
    
  
Lemma main_NI : @NI _ _ (eqsum_R (publicRel _ ) (semiprivateRel _))
                  my_f_out_rel
                  (@map _ _ _ (Option (Option (Sum TPublicOutput TTypeSyscall))) my_f_in my_f_out
                     (my_loop_and_count
                        (@scheduled_process_pool 2 my_f_I my_f_O (@my_f_sch my_f_I) my_procs))).
Proof.
  eapply map_NI. 
  instantiate (1:= eqsum_R (publicRel Unit) (eqsum_LR (semiprivateRel THandlerOutput) (semiprivateRel TInterrupt))).

  mrw. intros.
  have: is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'. de i. de i'. de i'.
  case;split_and. de i. de i'. subst. de u.
  de i. de i'.
  mrw. intros.
  destruct i. rewrite /my_f_in. destruct i.
  ssa. ssa.

  mrw. intros. move: H. instantiate (1:= intermediate_outputRel ). (*replaced eqpair_OR with eqpair_LR because we need enough information about distinguishability so that we don't do None vs Some case distinction in i1 and i2 when relating (x,i1,y) and (x',i2,y) *)
  (*we needed eqpair_OR because we used eqmaybe in secret processes*)
  (*we did that to get (none,none,none) as public*)
  (*more generally we did it to minimise what is distinguished*)
  (*eqpair_LR makes (none,none,none) private*)
  (*what does this mean for the output type the word sees?*)
  intros. 
  destruct i,i'. destruct i0,i2.
  apply rel_eqpair in H. destruct H.
  apply rel_eqpair in H0. destruct H0.
  rewrite !pair_rewr in H,H0,H1.
  apply rel_eqmaybe2 in H,H0,H1.
  destruct H. split_and;subst.
  destruct H0. split_and;subst.
  destruct H1. split_and;subst.
  split_and;subst.
  split_and;subst.
  destruct H1. split_and;subst. ssa.
  split_and;subst. ssa. subst. ssa.
  split_and;subst.
  destruct H0. split_and;subst.
  destruct H1. split_and;subst. ssa.
  split_and;subst. ssa.
  split_and;subst.
  destruct H1. split_and;subst. ssa.
  split_and;subst. ssa.

  apply/map_NI.
  4: apply/loop_NI.
  mrw. intros. apply rel_eqsum_L. (*R = output, not distinguished*) eapply H.
  mrw. intros. apply dis_eqsum_L. done.

  instantiate (1:= intermediate_outputRel). 

  mrw. intros.
  have: is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'. de i. de i'. de i'.
  case;split_and. de i. de i'. de i'. de i'.
  de i. de i'. de i'. de i'.

  eapply map_NI.
  4: apply sta_NI.
  apply f_NI_id.
  apply f_PU_id. 
  
  mrw. intros. apply rel_eqpair in H. destruct H. eauto.


  (*Trying to work on side conditions here, should not affect the rest of the proof because of 4: {*)
  2: { mrw. intros. eapply H0. } 
  shelve.
  mrw. intros. eauto.

(*  instantiate (1:=  publicRel _).*)
(*  mrw;ssa.
  mrw;ssa.
  mrw;ssa.*)

  eapply map_NI. 

  instantiate (1:= eqpair_R _ (eqmaybe (eqsum_R (publicRel Unit) (eqsum_LR (semiprivateRel THandlerOutput) (semiprivateRel TInterrupt))))). (*eqmaybe is correct? I think we need eqmaybe_top instead*)
  mrw. intros.
  destruct i. destruct i'. rewrite !pair_rewr.
  have: is_inl i0 /\ is_inl i2 \/ is_inr i0 /\ is_inr i2. ssa. de H. subst. de i0. de i2. de i2. de i0. de s. de s. subst. de i2. de i2.
  case;split_and. destruct i0. destruct i2.
  apply rel_eqpair_R2.  
  apply rel_eqpair_R2' in H. destruct H. split_and. split_and. ssa. ssa.

  destruct i0. ssa.
  destruct i2. ssa.
  apply rel_eqpair_R2' in H. destruct H. split_and.
  apply rel_eqsum_L2' in H2.
  destruct i0,i3,i2,i5.
  rewrite /map_pair /my_f_route.
  have: is_some i4 /\ is_some i6 \/ is_none i4 /\ is_none i6. de i4. de i6. de i6.
  case;split_and. destruct i4. 2:ssa. destruct i6. 2:ssa.
  rewrite /intermediate_outputRel in H2.
  apply rel_eqpair in H2. split_and.
  apply rel_eqpair in H5. split_and.
  rewrite !pair_rewr in H2 H5 H6.
  apply rel_eqpair_R2. left. con. eauto.
  apply rel_eqmaybe. ssa.
(*  apply rel_eqsum_R2.
  apply rel_eqsum_LR.
  apply rel_eqmaybe2 in H6. destruct H6. split_and. inversion H6. inversion H7. subst. done.
  split_and. rewrite H6 in H3. ssa.*)
  apply rel_eqpair_R2. left. con. eauto. destruct i4. done. destruct i6. done. ssa.
  split_and.
  apply rel_eqpair_R2. right. con.
  ssa. ssa.

  mrw. intros. destruct i. rewrite !pair_rewr.
  apply dis_eqpair_R in H.
  destruct i0. 2: ssa.
  apply dis_eqsum_L2 in H.
  destruct i0. ssa.
  apply dis_eqsum_R2 in H.
  apply dis_eqpair_R2.
  apply dis_eqmaybe2. done.
(*  apply dis_eqsum_R. done.*)

  mrw. intros.
  apply rel_eqsum_L2. eauto.

(*  move: H. instantiate (1:= publicRel _). (*because conclusion relates inr by eqsum_L*)
  intros. simpl in H. subst.
  apply rel_eqsum
  simpl in H. subst. ssa. ssa. ssa.
  destruct i4. ssa. destruct i6. ssa.
  simpl in H. subst. ssa.
  split_and.
  ssa.

  mrw. intros. ssa. de i. de s.

  mrw. intros.
  apply rel_eqsum_L2. eauto.*)

  instantiate (1:= (publicRel _)).
  rewrite /scheduled_process_pool.
  rewrite /nat_rec. rewrite /nat_rect.

  eapply par_NI.
  eapply map_NI.
  instantiate (1:= eqpair_R (publicRel _) (eqmaybe_top (publicRel _))).
  mrw. intros.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2.
  destruct H. left. split_and. simpl in H. rewrite H. ssa.
  destruct i. destruct i'. simpl in H. subst. 
  
  rewrite /option_inl_some !pair_rewr. rewrite !pair_rewr in H0.
  apply rel_eqmaybe2 in H0. destruct H0. split_and. subst. 
  destruct x. destruct x0.
  apply rel_eqmaybe.
  apply rel_eqsum_R' in H1. done. ssa. destruct x0. ssa.
  apply rel_refl.
(*  destruct H. split_and. subst. destruct x. ssa. apply rel_refl.
  destruct H. split_and. subst. de x. *)
  split_and. subst. ssa. right.
  split_and.
  clear H0. ssa. de i. de o. de s. de s.
  clear H. ssa. de i'. de o. de s. de s.
  
  mrw. intros. ssa. de i. de o. de s. de s.
  apply f_NI_id.

(*  eapply NI_I_imp. Check swi_NI.
  instantiate (1:= (eqpair_LR (publicRel Bool) (eqmaybe_top (publicRel (my_f_I 2))))).
                      (eqmaybe (eqsum_R (publicRel Unit) (eqsum_LR (semiprivateRel THandlerOutput) (semiprivateRel TInterrupt)))))).
  ssa. de x. de o. de s. de s.
  intros. ssa. de H. de x. de o. de s. de s. de H. de x. de o. de s. de s. de y. de o. subst.
  de s. de s. subst. de y. de o. de s. de s.*)

  1: { admit.

    


(*  apply swi_NI. Check sta_NI. Check swi_NI.
  intros.
  destruct (eqVneq l \bot). subst.
  right.

  pcofix CIH. pfold. con. intros.

  match_dd_o.  de i0. inv x.
  destruct i0. have: Nothing == Notify = false. done. move=>->. eauto.
  rewrite eqxx.
  left. pcofix CIH2.
  pfold. con. intros.
  match_dd_o.

  intros. match_dd_o. con. eauto. ssa.
  intros. con. match_dd_o. ssa.
  left. rewrite /aware. intros. simpl in H. destruct H. ssa. subst. rewrite eqxx in i. done.

  eapply NI_I_imp.
  3: apply maybe_NI.
  intros. apply dis_eqmaybe in H. split_and. subst.
  apply dis_eqmaybe_false2. eauto.
  ssa. de x. de y. de y.

  eapply map_NI.
  mrw. intros.
  4: apply maybe_NI.
  destruct (eqVneq l \bot). subst. destruct i. destruct i'. rewrite /inl_some.
  apply rel_eqmaybe_top2. apply rel_eqsum_LR' in H. eauto. ssa.
  destruct i'. ssa. ssa.
  ssa. de i. de i'. de i'.

  mrw. intros. de i.

  mrw. intros. apply rel_eqpair_LR2. con. apply rel_refl. eauto.
  simpl. rewrite /high_p2. rewrite /alternate_generic2.

  eapply map_NI.
  mrw. intros. apply rel_eqsum_L. eauto.
  mrw. intros. apply dis_eqsum_L. done.
  mrw. intros. move: H.
  instantiate (1:= eqsum_L _ _). intros.
  destruct i. destruct i'. apply rel_refl. ssa.
  destruct i'. ssa.
  apply rel_eqsum_R2' in H.
  destruct i. destruct i0.
  2: apply loop_NI.
  destruct i1. destruct i2.
  shelve.
  
  eapply map_NI.
  apply f_NI_id.
  apply f_PU_id.

  mrw. intros. apply rel_eqsum_L2. eauto.

  apply sta_NI.
  mrw. intros. eauto.
  mrw. intros.
  destruct i. destruct i'. apply rel_eqsum_L' in H.
  instantiate (1:= semiprivateRel _). ssa. de H. de H0. subst. left. ssa.
  ssa. destruct i'. ssa. apply rel_refl.
  mrw. intros. destruct i. apply dis_eqsum_L2 in H. ssa. ssa.
  apply out_NI.
  
  Unshelve.
  2: { mrw. intros. ssa. } *)

}




  

  (*next process*)
  eapply map_NI.
  mrw. intros. rewrite /map_pair. destruct i,i'.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2.
  destruct H. split_and. 
  left. con. eauto.
  apply rel_eqmaybe2 in H0. destruct H0. split_and. subst.
  instantiate (1:=  (eqmaybe (eqsum_LR (semiprivateRel THandlerOutput) (semiprivateRel TInterrupt)))).
  destruct x. destruct x0. ssa. ssa. destruct x0. ssa.
  apply rel_eqmaybe. ssa. split_and. subst. ssa. split_and.
  right. con. ssa. de i0. de s. de i2. de i2.
  mrw. intros. ssa. de i. de o. de s.
  apply f_NI_id.

  apply par_NI.

  eapply map_NI.
  instantiate (1:= eqpair_R _ _).
  mrw. intros.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2.
  destruct H. split_and. 
  left. con. rewrite /my_f_sch. instantiate (1:= semiprivateRel _). rewrite H. apply rel_refl.

  destruct i. destruct i'. rewrite /option_inl_some !pair_rewr. rewrite !pair_rewr in H0.
  instantiate (1:= eqmaybe_top _).
  destruct i0. destruct i2.
  apply rel_eqmaybe2 in H0. destruct H0. split_and. inversion H0. inversion H1. subst.
  destruct x. destruct x0.
  apply rel_eqmaybe.
  apply rel_eqsum_LR' in H2. eauto. ssa.
  destruct x0. ssa. ssa. ssa. ssa. destruct i2. ssa. ssa.
  split_and. right. con.
  clear H0. ssa. de i. de o. de s.
  clear H. ssa. de i'. de o. de s. 

  mrw. intros. ssa. de i. de o. de s.
  apply f_NI_id.

  eapply NI_I_imp.
  instantiate (1:= (eqpair_LR (semiprivateRel Bool)
                      (eqmaybe (semiprivateRel THandlerOutput)))).
  ssa. de x. de o. de x. de o.
  ssa. de H. de x. de o. de s. de H. de x. de o. de s. subst. de y. de o. de s. subst.
  de y. de o. de s.


  apply swi_NI.
  intros.
  destruct (eqVneq l \bot). subst.*)
  right.

  pcofix CIH. pfold. con. intros.

  match_dd_o.  de i0. inv x.
  destruct i0. have: Nothing == Notify = false. done. move=>->. eauto.
  rewrite eqxx.
  left. pcofix CIH2.
  pfold. con. intros.
  match_dd_o.

  intros. match_dd_o. con. eauto. ssa.
  intros. con. match_dd_o. ssa.
  left. rewrite /aware. intros. simpl in H. destruct H. ssa. subst. rewrite eqxx in i. done.

  eapply NI_I_imp.
  3: apply maybe_NI.
  intros. apply dis_eqmaybe in H. split_and. subst.
  apply dis_eqmaybe_false2. eauto.
  ssa. de x. de y. de y.

  eapply map_NI.
  mrw. intros.
  4: apply maybe_NI.
  destruct (eqVneq l \bot). subst. destruct i. destruct i'. rewrite /inl_some.
  apply rel_eqmaybe_top2. apply rel_eqsum_LR' in H. eauto. ssa.
  destruct i'. ssa. ssa.
  ssa. de i. de i'. de i'.

  mrw. intros. de i.

  mrw. intros. apply rel_eqpair_LR2. con. apply rel_refl. eauto.
  simpl. rewrite /high_p2. rewrite /alternate_generic2.

  eapply map_NI.
  mrw. intros. apply rel_eqsum_L. eauto.
  mrw. intros. apply dis_eqsum_L. done.
  mrw. intros. move: H.
  instantiate (1:= eqsum_L _ _). intros.
  destruct i. destruct i'. apply rel_refl. ssa.
  destruct i'. ssa.
  apply rel_eqsum_R2' in H.
  destruct i. destruct i0.
  2: apply loop_NI.
  destruct i1. destruct i2.
  shelve.
  
  eapply map_NI.
  apply f_NI_id.
  apply f_PU_id.

  mrw. intros. apply rel_eqsum_L2. eauto.

  apply sta_NI.
  mrw. intros. eauto.
  mrw. intros.
  destruct i. destruct i'. apply rel_eqsum_L' in H.
  instantiate (1:= semiprivateRel _). ssa. de H. de H0. subst. left. ssa.
  ssa. destruct i'. ssa. apply rel_refl.
  mrw. intros. destruct i. apply dis_eqsum_L2 in H. ssa. ssa.
  apply out_NI.
  
  Unshelve.
  2: { mrw. intros. ssa. } 

  (*final process*)
  fold interp.
  eapply map_NI.
  mrw. intros. rewrite /map_pair. destruct i,i'.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2.
  destruct H. split_and. 
  left. con. eauto.
  apply rel_eqmaybe2 in H0. destruct H0. split_and. subst.
  instantiate (1:=  (eqmaybe_top ((semiprivateRel TInterrupt)))). (*eqmaybe_top instead of eqmaybe*)
  destruct x. destruct x0. ssa. ssa. destruct x0. ssa.
  apply rel_eqmaybe. ssa. split_and. subst. ssa. split_and.
  right. con. ssa. de i0. de s. de i2. de i2.
  mrw. intros. ssa. de i. de o. de s.
  apply f_NI_id.

  eapply map_NI.
  instantiate (1:= eqpair_R _ _).
  mrw. intros.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2.
  destruct H. split_and. 
  left. con. rewrite /my_f_sch. instantiate (1:= semiprivateRel _). simpl in H. rewrite H. apply rel_refl. eauto.
  split_and.
  mrw. intros. ssa.
  apply f_NI_id.

  eapply NI_I_imp.
  instantiate (1:= (eqpair_LR (semiprivateRel Bool)
                      (eqmaybe_false (((semiprivateRel TInterrupt)))))). (*eqmaybe_false was necessary here, do we need it in the high proc too???*)
  ssa. de x. de o. de x. de o.

  ssa. de H. de x. de o.
  de H. de H. subst. de x. de o. de y. de o. subst. de y. de o. subst.
  de x. de o. de y. de o. de y. de o. de x. de y. de o. de o0. de o0.

  simpl. rewrite /handler. 
  apply swi_NI.
  intros.
  destruct (eqVneq l \bot). subst.
  right.

  pcofix CIH. pfold. con. intros.

  match_dd_o. left. pcofix CIH2.
  pfold. con.
  intros. match_dd_o.
  intros. match_dd_o. con. eauto. ssa.

  intros. match_dd_o. con. eauto. ssa.
  intros. 
  left. rewrite /aware. intros. simpl in H. destruct H. ssa. subst. rewrite eqxx in i. done.

  eapply NI_I_imp.
  3: apply maybe_NI.
  intros. eauto.

  intros. done.



  eapply map_NI.
  apply f_NI_id.
  apply f_PU_id.
  
  (*Why could we just remove this chunk in the final part???*)  
  (*mrw. intros.
  4: apply maybe_NI.
  destruct (eqVneq l \bot). subst. destruct i. destruct i'. rewrite /inl_some.
  apply rel_eqmaybe_top2. apply rel_eqsum_LR' in H. eauto. ssa.
  destruct i'. ssa. ssa.
  ssa. de i. de i'. de i'.

  mrw. intros. de i. *)


  mrw. intros. apply rel_eqpair_LR2. con. apply rel_refl. eauto.
  simpl. rewrite /alternate_generic.

  eapply map_NI.
  mrw. intros. apply rel_eqsum_L. eauto.
  mrw. intros. apply dis_eqsum_L. done.
  mrw. intros. move: H.
  instantiate (1:= eqsum_L _ _). intros.
  destruct i. destruct i'. apply rel_refl. ssa.
  destruct i'. ssa.
  apply rel_eqsum_R2' in H.
  destruct i. destruct i0.
  2: apply loop_NI.
  destruct i1. destruct i2.
  shelve.
  
  eapply map_NI.
  apply f_NI_id.
  apply f_PU_id.  
  mrw. intros. apply rel_eqsum_L2. eauto.

  apply sta_NI.
  mrw. intros. eauto.
  mrw. intros.
  destruct i. destruct i'. apply rel_refl. ssa.
  destruct i'. ssa. apply rel_refl.
(*  apply rel_eqsum_L' in H.
  instantiate (1:= semiprivateRel _). ssa. de H. de H0. subst. left. ssa.
  ssa. destruct i'. ssa. apply rel_refl.*)
  mrw. intros. destruct i. apply dis_eqsum_L2 in H. ssa.
  instantiate (1:= semiprivateRel _). ssa. ssa.
  apply out_NI.
  apply rel_eqpair in H. split_and. rewrite !pair_rewr in H H0.
  ssa. destruct H. ssa. subst. left. ssa. auto.
  apply publicRel.
  
  Unshelve.
  apply rel_eqpair in H. split_and. rewrite !pair_rewr in H H0. ssa. destruct H. ssa. subst. eauto. auto.
  apply publicRel.
Qed.
















  



  
  simpl in H. destruct i,i'. rewrite !pair_rewr in H. subst.
  rewrite !pair_rewr in H0.
  rewrite !pair_rewr.
  apply rel_eqmaybe2 in H0.
  destruct H0. split_and. subst. 
  
  apply rel_eqpair_LR2. con.
  apply rel_eqmaybe. eauto.
  apply rel_eqmaybe. eauto.
  split_and;subst. ssa.
  split_and.
  apply rel_eqpair_LR2. con. ssa.
  apply dis_dis_rel. done. done.

  destruct i,i'.
  rewrite !pair_rewr in H,H0.
  rewrite !pair_rewr.
  apply dis_dis_rel. ssa.
  have: i0 <> None. de i0.
  intros. have: i2 <> None by de i2.
  intros.
  destruct i0.
  ssa. de s. de s. de i2. de s. de s. 
  destruct i2. simpl. de s. de s
  apply rel_eqpair_LR2. con. ssa.
  mrw. ssa.
  apply f_NI_id.

  Check swi_NI.
  eapply map_NI.
  left. con. ssa.
  apply rel_eqmaybe. eauto.
  right. ssa.
  ssa.
  
  de i'. de i'.
  de i. de i'. de i'. de i'.  
      destruct H.
  - split_ando. 
    apply rel_eqpair_OR in H0.
    destruct H0.
    * split_and. (*rel*)
      apply rel_eqmaybe_top in H;simpl in H.
      destruct H.
      ** split_and;subst. (*Some,Some*)
         apply rel_eqmaybe2 in H0;simpl in H0.
         destruct H0.
         *** split_and. subst.
             destruct H2;subst.
             **** apply rel_eqmaybe2 in H1;simpl in H1.
                  destruct H1. split_and.
             **** destruct H.
                  ***** split_and.
                  ***** split_and.
         *** apply rel_eqmaybe2 in H1;simpl in H1.
             destruct H1. 
             **** split_and.
             **** split_and.
      ** destruct H. (*Some,None*)
         *** split_and. subst.
             apply rel_eqmaybe2 in H1;simpl in H1.
             destruct H1.
             **** split_and. subst.
                  de H1.
             **** destruct H.
                  ***** split_and. subst.
                        rewrite /my_f_out. apply rel_eqmaybe_top_right.
                        apply dis_Some.

    * (*dis*)
  
  
Lemma main_NI : @NI _ _ (semiprivateRel _)
                  (eqmaybe (eqmaybe_top (eqsum_R (publicRel _) (semiprivateRel _))))
                  (@map _ _ _ (Option (Option (Sum TPublicOutput TTypeSyscall))) my_f_in my_f_out
                     (my_loop_and_count
                        (@scheduled_process_pool 2 my_f_I my_f_O (@my_f_sch my_f_I) my_procs))).
Proof.
  eapply map_NI.

  mrw. intros. rewrite /my_f_in.
  apply rel_eqsum_R2. apply rel_eqsum_R2. apply H.

  mrw. intros. rewrite /my_f_in. ssa.

  mrw. intros. move: H. instantiate (1:= eqpair_OR (eqmaybe_top (publicRel _)) (eqpair_OR (eqmaybe (semiprivateRel _)) (eqmaybe (semiprivateRel _)))).
  intros. 
  destruct i,i'. destruct i0,i2.

  apply rel_eqpair_OR in H.
    destruct H.
  - split_ando. 
    apply rel_eqpair_OR in H0.
    destruct H0.
    * split_and. (*rel*)
      apply rel_eqmaybe_top in H;simpl in H.
      destruct H.
      ** split_and;subst. (*Some,Some*)
         apply rel_eqmaybe2 in H0;simpl in H0.
         destruct H0.
         *** split_and. subst.
             destruct H2;subst.
             **** apply rel_eqmaybe2 in H1;simpl in H1.
                  destruct H1. split_and.
             **** destruct H.
                  ***** split_and.
                  ***** split_and.
         *** apply rel_eqmaybe2 in H1;simpl in H1.
             destruct H1. 
             **** split_and.
             **** split_and.
      ** destruct H. (*Some,None*)
         *** split_and. subst.
             apply rel_eqmaybe2 in H1;simpl in H1.
             destruct H1.
             **** split_and. subst.
                  de H1.
             **** destruct H.
                  ***** split_and. subst.
                        rewrite /my_f_out. apply rel_eqmaybe_top_right.
                        apply dis_Some.

    * (*dis*)

                  
        
  destruct H1. subst. ssa. ssa.
  destruct H. split_ando. subst. simpl. 
  
  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac. rewrite /my_f_out.
  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.

  
  move: H. instantiate (1:= eqpair_R (publicRel _) (eqpair_LR (eqmaybe_top (semiprivateRel _)) (eqmaybe_top (semiprivateRel _)))).
  intros. destruct i,i'.
  ssa.

                       

  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.

  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.    
  destruct H. ssa. subst. destruct H0.
  de i0. de o. de i2. de o. de H. subst. de o0. de H1. de o1.
  de H. subst. de i1. de i1. de o1. de i1. de i1. de H1. de o1. de i1.
  de o1. subst. de i1. de i1. de o0. de H1. de o1. de H0. subst.
  de i1. subst. de i1. de o1. subst. de i1. de i1. de H1. de o1. subst.
  de i1. subst. de o1. subst. de i1. de i1. de H1. de i2. de o.
  de o0. de o1. de H0. subst. de i1. subst. de i1. de o1. de i1. de i2. de o. de o0.
  subst. de o1. de i1. de i1. de o1. subst. de i1. de i1. ssa.
  de i0. de o. de i2. de o. subst. de o0. de H
1  de o0.
  
  rewrite /my_f_out. destruct i. destruct i1.
  apply rel_eqmaybe.
  apply rel_eqsum_R. ssa.












  
(*Lemma rel_inl : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]), rel (eqsum_L ARel BRel) ((inl \o f) ) ()*)
(*Lemma eqsum_R2 : forall (A B B' : Ty) l (x y : [A] + [B]) (f : [B] -> [B']) (ARel : myrel [A]) (BRel : myrel [B]) (BRel' : myrel [B']),
    f_NI BRel BRel' f -> rel (eqsum_R ARel BRel) l x y -> rel (eqsum_R ARel BRel') l x (f y).*)
Lemma rel_eqsum_LR3 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l x y, rel (eqsum_LR ARel BRel) l x y -> (exists x' y', x = inl x' /\ y = inl y' /\ rel ARel l x' y') \/ (exists x' y', x = inr x' /\ y = inr y' /\ rel BRel l x' y') \/ (exists x' y', x = inl x' /\ y = inr y' /\ dis ARel l x' /\ dis BRel l y') \/  (exists x' y', x = inr x' /\ y = inl y' /\ dis BRel l x' /\ dis ARel l y').
Proof.
  intros. destruct x. destruct y. left. exists i. exists i0. con. auto. con. auto.
  apply rel_eqsum_LR' in H. done.
  right. right. left. exists i. exists i0. con. auto. con. auto.
  ssa.
  destruct y. right. right. right.
  exists i. exists i0. con. auto. con. auto. ssa.
  right. left. exists i. exists i0. con. auto. con. auto.
  apply rel_eqsum_LR2' in H. done.
Qed.

Lemma interp_eq : (fix interp (t : Ty) : Set :=
       match t with
       | Nat => nat
       | Times t0 t1 => (interp t0 * interp t1)%type
       | Bool => bool
       | Option t' => option (interp t')
       | Sum t0 t1 => (interp t0 + interp t1)%type
       | TInput => Input
       | TOutput => Output
       | TTypeSyscall => TypeSyscall
       | Unit => unit
       | TInterrupt => Interrupt
       | THandlerOutput => HandlerOutput
       | TPublicOutput => PublicOutput
       | TPublicInput => PublicInput
       end) = interp.
  done.
Qed.

Lemma rel_top_false : forall (A : Ty) (ARel : myrel [A])l x y, rel (eqmaybe_top ARel) l x y -> rel (eqmaybe_false ARel) l x y.
Proof.
  intros. ssa. de x. de H. de y. de H. de y.
Qed.  

  
Lemma NI_main : @NI _ _ InputRel' OutputRel' (mitigator2 process_pool2).
Proof.  
  rewr. 
  eapply (@map_NI _ _ _ _ _ _ _ _ LoopTypeRel LoopTypeRel). 
  
  mrw. intros. rewrite /comp. apply rel_eqsum_LR. 
  de i. de i'. de i'. de H. subst. auto.

  mrw. ssa. de i.

  mrw. intros. rewrite /collapse_in_out.
  de i. de i'. de i. de p. de o. de i'. de i'. de i. de o. de i'.
  
  apply loop_NI.

  eapply map_NI.

  mrw. intros.
  instantiate (1:= eqsum_LR InterRel (semiprivateRel _)).
  de i. de i'. de i'.

  mrw. intros. de i.

  instantiate (1:= eqpair _ _). mrw. intros.
  destruct i,i'.
  rewrite !pair_rewr.
  apply rel_eqpair in H. destruct H.
  eauto.
  
  eapply sta_NI.

  mrw. intros.
  instantiate (1:= publicRel _). ssa. (*public rel for state*)

  mrw. intros. done.

  mrw. intros. done.

  eapply map_NI.

  instantiate (1:= eqmaybe_false (eqmaybe_false InterRel)).
  mrw. intros. destruct i,i'.
  rewrite !pair_rewr.
  apply rel_eqpair_R2' in H.
  destruct H. destruct H.

  apply rel_eqsum_LR3 in H0.
  destruct H0. destruct H0. destruct H0.
  destruct H0. destruct H1. subst.
  have: i = i1. ssa. move=>->.
  have: is_inr x = is_inr x0. de x. de x0. de x0.
  move=>->.
  case_if.
  apply/rel_eqmaybe.
  apply/rel_eqmaybe.
  done.
  ssa.
  destruct H0.
  destruct H0. destruct H0. destruct H0. destruct H1.
  subst.
  have: i = i1. ssa. move=>->.
  case_if. apply/rel_eqmaybe. ssa. ssa.

  destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
  destruct H2. subst.
  have: i = i1. ssa. move=>->.
  apply/dis_dis_rel. case_if. ssa. ssa.
  case_if. ssa. ssa.
  destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
  subst.
  apply/dis_dis_rel. case_if. done. done.
  case_if. done. done.
  destruct H.
  destruct i0. destruct i2.
  destruct i0. ssa.
  destruct i2. ssa.
  rewrite /is_inr orbC. rewrite /orb.
  case_if. apply dis_dis_rel. done. done. 
  move: H1. case_if. done. done.
  destruct i0. ssa. rewrite /is_inr orbC /orb.
  apply dis_dis_rel. done. case_if. done. done.
  destruct i2. destruct i2. ssa.
  rewrite /is_inr orbC /orb. case_if.
  apply dis_dis_rel. done. done.
  apply dis_dis_rel. done. ssa.
  apply dis_dis_rel.
  case_if. done. done.
  case_if. done. done.

  mrw. intros. destruct i. rewrite pair_rewr.
  apply dis_eqpair_R in H.
  destruct i0. destruct i0. ssa. rewrite !pair_rewr.
  rewrite /is_inr orbC /orb. ssa.
  destruct i0. rewrite pair_rewr.
  case_if. ssa. ssa.

  instantiate (1:= OutputRel').
  mrw. intros. auto.

(*  eapply NI_I_imp.
  instantiate (1:= eqmaybe_false (eqmaybe_false InterRel)). ssa.
  de x.
  intros. apply rel_top_false. done.*)

  apply maybe_NI.

  eapply map_NI.

  instantiate (1:= eqpair_LR boolRel (eqmaybe_false InterRel)).
  mrw. intros.

  de i. de i'. de H. de i. de H. de i'. de i'. de s.

  mrw. intros. de i. de i.

  

(*  Check par_NI.
  
  apply swi_NI. shelve.

  apply maybe_NI.

  2: { apply swi_NI. shelve. apply maybe_NI. shelve. }

  Unshelve.

  2: { mrw. intros.
       instantiate (1:= InterRel).
       instantiate (1:= privateRel _). ssa. } 


  instantiate (1:= eqpair_LR (publicRel _) (eqmaybe_top InterRel)). (*None maps to true, so we make the whole bool private to preserve from None*) (*problem in oblivious/output case, now trying publicRel*)
  mrw. intros.
  destruct i. destruct i'.
  apply rel_eqpair_LR2. con. ssa. done.
  ssa. de H. de i. (*Something interesting happened here, worried this would not be true*)
  destruct i'.
  ssa. de H. de i. ssa.

  mrw. intros. de i. de i. de (eqVneq l \bot). exfalso. apply/H.
  apply/eqP. done.*)

  apply f_NI_id.

  eapply NI_O_imp.
  instantiate (1:= eqpair _ _).
  intros. apply rel_eqpair in H. destruct H.
  destruct x. destruct y.
(*  Search _ (rel (eqpair_R _ _)).*)
  apply rel_eqpair_LR2. (*Since switch to *_LR. MAYBE WRONG*)
  rewrite !pair_rewr in H H0.
  con. eauto. eauto.

  apply par_NI.

  apply swi_NI.

  intros.
  right.

  left. rewrite /aware. intros. simpl in H. de H. subst.
  intro.
  de (eqVneq l \bot). subst. right.

  pcofix CIH.
  pfold. con. 
  intros;match_dd_once;eauto.
  match_dd_once. match_dd_once.
  right. eauto. rewrite /inl_some in x. de i0.
  match_dd. left. pcofix CIH2. pfold. con.
  intros.
  match_dd_once. eauto.
  match_dd_once. match_dd_once.
  right. eauto.
  match_dd. right. eauto.
  
  intros.
  match_dd. con. admit. simpl.
  
  move: CIH. rewrite /alternate_generic2.
  left. pfold. con. intros. match_dd_once.
  admit. 
  right. eauto.
  intros;match_dd_once;eauto;left;pfold;con.  
  match_dd_once. left.
  pfold. con. intros.
  match_dd_once. left.
  pfold. con. intros.
  match_dd_once. left.
  pfold. con. intros.
  match_dd_once.
  left. rewrite /aware. intros. simpl in H. destruct H. ssa.
  intro. apply/negP. apply i. apply/eqP. done. move/eqP : H.
  move/negbTE : i. move=>->. done.
  
End Example3.
