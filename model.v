Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import RelationClasses.
From Paco Require Import paco.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
Require Import Stdlib.Streams.Streams.
From HB Require Import structures.
From deriving Require Import deriving.
Require Import Coq.Program.Equality.
From Equations Require Import Equations.
Require Import Coq.Classes.DecidableClass.

Import Order.TTheory.
Open Scope order_scope.

Parameter (level : tbLatticeType (Order.Disp tt tt)).

Ltac con := constructor.
Ltac econ := econstructor.
Ltac inv H := inversion H;subst.
Ltac econs := try do ? econ; done.
                     
Ltac split_ando :=
  intros;
   repeat
    match goal with
    | H:is_true (_ && _) |- _ => destruct (andP H); clear H
    | H:_ && _ = true |- _ => destruct (andP H); clear H
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
           _: forall l a0 a1, dis l a0 -> rel l a0 a1 -> dis l a1

          }.

(*Existing Class myrel. 
Hint Mode myrel +.*)

(* Types *)

(*Example 3*)
Inductive Interrupt := DiskInterrupt | TimerInterrupt.
Inductive HandlerOutput := Nothing | Notify.
Inductive TypeSyscall := Syscall.
Inductive PublicOutput := GetRequest.

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

Inductive Ty : Set := Nat | Times : Ty -> Ty -> Ty | Bool | PrivateBool
                 | Option : Ty -> Ty | Option_swi : Ty -> Ty | Option_maybe : Ty -> Ty | Sum : Ty -> Ty -> Ty | TInput | TOutput | TTypeSyscall | Unit | TInterrupt | THandlerOutput |  TPublicOutput. 

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
  | Bool | PrivateBool => bool
  | Option t' | Option_swi t' | Option_maybe t' => option (interp t')
  | TInput => Input
  | TOutput => Output
  | Sum t0 t1 => (interp t0) + (interp t1)            
  | TTypeSyscall => TypeSyscall
  | Unit => unit                     
  | TInterrupt => Interrupt
  | THandlerOutput => HandlerOutput
  | TPublicOutput => PublicOutput
  end.
Notation "[ i ]" := (interp i).







(** Process type **)
Inductive Proc : Ty -> Ty -> Type :=
| out  : forall {I O : Ty}, interp O -> Proc I O  
| map   : forall {I I' O O' : Ty}, (interp I -> interp I') -> (interp O -> interp O') -> Proc I' O -> Proc I O'
| sta   : forall {I O V :Ty}, (interp I -> interp V -> interp V) -> (interp O -> interp V -> interp V) -> interp V -> Proc (Times V I) O -> Proc I (Times V O)
| swi   : forall {I O : Ty},  bool -> Proc I (Times Bool O)%type -> Proc ((Times Bool I)) (Option_swi O)
| par   : forall {I O1 O2: Ty}, Proc I O1 -> Proc I O2 -> Proc I (Times O1 O2)
| loop  : forall {I : Ty}, Proc I I -> Proc I I
| maybe : forall {I O: Ty}, Proc I O -> Proc (Option_maybe I) O.
Arguments out {_} {_} o.
Derive NoConfusion for Proc.
Derive NoConfusionHom for Proc.
Derive Signature for Proc.

Definition xor (b1 b2 : bool) := (Datatypes.negb (b1 == b2)).


Inductive reduceI : forall (I O : Ty), Proc I O -> interp I -> Proc I O -> Prop :=
| reduce_outI I O i (o : [O]) : reduceI (@out I _ o) i (@out I _ o)
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
| reduce_outO (I O : Ty) (o : [O]) : reduceO (@out I _ o) o (@out I _ o)
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

Ltac match_dd := 
   repeat
    match goal with
    | H : reduceI ?p _ _ |- _ => check_if_var p; dependent destruction  H
    | H : reduceO ?p _ _ |- _ => check_if_var p; dependent destruction  H
    end.

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

Definition privateRel (A : Ty) : myrel ([A]).
  refine (@MyRel _
            (fun l b => True)
            (fun l b1 b2 => b1 = b2)
            _
            _
            _
            _).
intros.
done.
eauto.
eauto.
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

  - eauto. eauto.
Defined.

Definition eqpair_LR {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Times I O]).
  refine (@MyRel _ 
            (fun (l : level) io => dis IRel l (fst io) \/ dis ORel l (snd io))
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

  - intros. de IRel;de ORel.
    de H0;eauto.
  - intros. de IRel;de ORel.
    de H;eauto.
Defined.

Definition eqpair_L {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Times I O]).
  refine (@MyRel _ 
            (fun (l : level) io => dis IRel l (fst io))
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

  - intros. de IRel;de ORel. eauto.
  - intros. de IRel;de ORel. eauto.
Defined.

Definition eqpair_R {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Times I O]).
  refine (@MyRel _ 
            (fun (l : level) io => dis ORel l (snd io))
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

  - intros. de IRel;de ORel. eauto.
  - intros. de IRel;de ORel. eauto.
Defined.

Lemma eqsum {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Sum I O]).
  refine (@MyRel _ 
            (fun (l : level) io => match io with | inl i => dis IRel l i | inr o => dis ORel l o end)
            (fun l io1 io2 => match io1,io2 with | inl i1,inl i2 => rel IRel l i1 i2 | inr o1,inr o2 => rel ORel l o1 o2 | _,_ => False end)
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
    move: (equiv1 l). case. eauto.


  -     ssa. de a0. de a1. de IRel. eauto.
        de a1. de ORel. eauto.

        ssa. de a. de IRel. eauto.
        de ORel. eauto.

        ssa. de a0. de a1. de IRel. eauto.
        de a1. de ORel. eauto.
Defined.

Definition levelPred := level -> Prop.

Definition eqmaybe {V : Ty} (P: levelPred) (VRel : myrel [V]) : myrel ([Option V]).
    refine (@MyRel _
            (fun l v => if v is Some v' then dis VRel l v' else ~ P l /\ forall x0 x1, order x0 x1 -> P x0 -> P x1 )
            (fun l b1 b2 => b1 = b2)
            _
            _
            _
            _).
intros. auto.
ssa. de a.
de VRel. eauto.
intro. apply H0. eauto.
intros. de a0. de a1. inv H0. subst. done.
subst. done.
Defined.

Definition eqmaybe_swi {V : Ty} (P: levelPred) (VRel : myrel [V]) : myrel ([Option_swi V]).
    refine (@MyRel _
            (fun l v => if v is Some v' then dis VRel l v' else ~ P l /\ forall x0 x1, order x0 x1 -> P x0 -> P x1 )
            (fun l b1 b2 => b1 = b2)
            _
            _
            _
            _).
intros. auto.
ssa. de a.
de VRel. eauto.
intro. apply H0. eauto.
intros. de a0. de a1. inv H0. subst. done.
subst. done.
Defined.

Definition eqmaybe_maybe {V : Ty} (P: levelPred) (VRel : myrel [V]) : myrel ([Option_maybe V]).
    refine (@MyRel _
            (fun l v => if v is Some v' then dis VRel l v' else ~ P l /\ forall x0 x1, order x0 x1 -> P x0 -> P x1 )
            (fun l b1 b2 => b1 = b2)
            _
            _
            _
            _).
intros. auto.
ssa. de a.
de VRel. eauto.
intro. apply H0. eauto.
intros. de a0. de a1. inv H0. subst. done.
subst. done.
Defined.

(*Definition eqmaybeT {V : Ty} (VRel : myrel [V]) : myrel ([Option V]) := eqmaybe VRel (fun _ => True).*)

Definition boolRel : myrel ([Bool]) := privateRel Bool. (*publicRel Bool.*)

Definition aware (V : Ty) (VRel : myrel [V]) (v : [V]) : levelPred
   := fun l => (forall v', rel VRel l v v' -> v = v' /\ ~ dis VRel l v').

Fixpoint to_rel (ty : Ty): myrel [ty]:=
      match ty as x return myrel [x] with
    | TInput => publicRel TInput
    | THandlerOutput => privateRel THandlerOutput
    | TInterrupt => privateRel TInterrupt
    | Option t => eqmaybe (fun _ => True) (to_rel t)
    | Option_swi t => eqmaybe (fun l => @aware Bool boolRel true l) (to_rel t)
    | Option_maybe t => eqmaybe (fun _ => False) (to_rel t)
    | Times t0 t1 => eqpair_LR (to_rel t0) (to_rel t1)
(*    | Times_L t0 t1 => eqpair_L (to_rel t0) (to_rel t1)
    | Times_R t0 t1 => eqpair_R (to_rel t0) (to_rel t1)
      | Times_LR t0 t1 => eqpair_LR (to_rel t0) (to_rel t1)
                                    *)
      | Sum t0 t1 => eqsum (to_rel t0) (to_rel t1)
      | PrivateBool => privateRel PrivateBool
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

Lemma rel_sym : forall A (ARel : myrel A) l x y, rel ARel l x y -> rel ARel l y x.
  Proof.
    intros. destruct ARel;ssa.
    move: (equiv0 l). case. ssa.
  Qed.
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
  simpl;debug_reduce;
    match goal with
    | |- reduceI (@out _ _ _) _ _ => apply: reduce_outI
    | |- reduceI (@map _ _ _ _ _ _ _) ?i _ => idtac "map_in" i;apply: reduce_mapI
    | |- reduceI (@sta _ _ _ _ _ ?v _) _ _ => idtac "state" v;apply: reduce_staI
    | |- reduceI (@swi _ _ _ _) _ _ => apply: reduce_swiI
    | |- reduceI (par _ _) _ _ => apply: reduce_parI
    | |- reduceI (@loop _ _) _ _ => apply: reduce_loopI                                                  
    | |- reduceI (@maybe _ _ _) None _ => apply: reduce_maybeI
    | |- reduceI (@maybe _ _ _) (Some _) _ => apply: reduce_maybeI2

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




Definition f_NI {I O :Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O]) := forall (l : level) (i i' : [I]) (o o' : [O]), rel IRel l i i' -> rel ORel l (f i) (f i').
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

Lemma map_NI : forall (I I' O O' : Ty) (p : Proc I' O) (f : [I] -> [I']) (g : [O] -> [O']) (IRel : myrel [I]) (IRel' : myrel [I']) (ORel : myrel [O]) (ORel' : myrel [O']),
    NI IRel' ORel p -> f_NI IRel IRel' f -> f_PU IRel IRel' f -> f_NI ORel ORel' g -> NI IRel ORel' (map f g p).
Proof. Admitted.


Lemma sta_NI : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O]),
    NI (eqpair_R VRel IRel) ORel p -> fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f -> f_EP IRel VRel f -> NI IRel (eqpair VRel ORel) (sta f g v p).
Admitted.

 (*fixed typo in paper: In conclusion, replaced I with Bool * I  *) 
Theorem swi_NI : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) p b, NI IRel (eqpair_LR boolRel ORel) p ->
(forall l, aware boolRel true l \/  oblivious (eqpair_R boolRel ORel) p l ) ->                                                                              
NI (eqpair_LR boolRel IRel) (eqmaybe_swi (fun l => aware boolRel true l) ORel) (swi b p).
 Admitted.

Theorem maybe_NI : forall (I O :Ty) (IRel : myrel [I]) (ORel : myrel [O]) p, NI IRel ORel p -> NI (eqmaybe_maybe (fun _ => False) IRel) ORel (maybe p).
Admitted.

Theorem loop_NI : forall (I : Ty) (IRel : myrel [I]) p, NI IRel IRel p -> NI IRel IRel (loop p).
Admitted.

Theorem par_NI : forall (I O1 O2 : Ty) (IRel : myrel [I]) (ORel1 : myrel [O1]) (ORel2 : myrel [O2]) p1 p2, NI IRel ORel1 p1 -> NI IRel ORel2 p2 -> NI IRel (eqpair ORel1 ORel2) (par p1 p2).
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
  : Proc (_ Bool (Times I1 I2)) (_ (Option_swi O1) (Option_swi O2)) :=
    par
      (swi b (@map (Times _ _) _ _ (Times_R Bool _) fst (fun x => (false,x)) p1))
      (swi (negb b) (@map (Times _ _) _ _ (Times_R Bool _) snd (fun x => (false,x)) p2)).*)


(*Not used for anything*) Check sta.
Definition scheduled_p (I O : Ty) (b : bool) (p : Proc I O) :=
  @map _ _ (Times _ _) _ id snd (*drop state*)
    (@sta (Times Bool _) _ Bool (fun i v => xor (fst i) v) (fun o v => v) b (*track swi flag*)
       (@map (Times _ (Times _ _))  (Times _ (Times _ _)) _ _ (fun i => (fst (snd i),(fst i,snd (snd i)))) id (*(v,(b,i)) -> (b,(v,i))*)
          (swi b (@map (Times Bool _) (Option_maybe _) _ (Times Bool _) (fun i => if fst i then Some (snd i) else None) (fun o => (false,o)) (*if b then send input to p*)
                    (maybe p))))).


Lemma par_swiI_NI : forall (I1 I2 O1 O2 : Ty) (b : bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (IRel1 : myrel [I1]) (IRel2 : myrel [I2]) (ORel1 : myrel [O1]) (ORel2 : myrel [O2]),
     NI IRel1 ORel1 p1 -> NI IRel2 ORel2 p2 -> NI (eqpair_LR boolRel (eqpair IRel1 IRel2)) (eqpair (eqmaybe_swi (aware boolRel true) ORel1) (eqmaybe_swi (aware boolRel false) ORel2)) (par_swiI b p1 p2).
Proof. Admitted.

(*sta_swi b n f p:
 (i == n,I') -> enables p
 (i <> n,I') -> disables p
 f projects input from pair e.g. f (I1,I2) = I1
 maybe is used to disgard input to p when i<>n.
 *)

Definition sta_swi (I' I O : Ty) (b : bool) (n : nat) (f : [I'] -> [I]) (p : Proc I O) :=
@map (Times Nat _) (Times Bool _) (Times _ _) _ (fun x => (fst x == n,snd x)) snd
  (@sta (Times Bool _) _ Bool
       (fun i v => xor (fst i) v)
       (fun o v => false)
       b
       (swi b (@map (Times Bool _) (Option_maybe _) _ (Times Bool _)
                    (fun i => if fst i then Some (f (snd i)) else None)
                    (fun o => (true,o))
                    (maybe p)
  ))).

Definition par_swiI3 {I1 I2 I3 O1 O2 O3} (n : nat) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (p3 : Proc I3 O3)
  : Proc (Times Nat (Times I1 (Times I2 I3))) (Times (Option_swi O1) (Times (Option_swi O2) (Option_swi O3))) :=
    par
      (@sta_swi (Times _ _) _ O1 (n == 0) 0 fst p1)
      (par
      (@sta_swi (Times _ (Times _ _)) _ O2 (n == 1) 1 (fun x => fst (snd x)) p2)
      ((@sta_swi (Times _ (Times _ _)) _ O3 (n == 2) 2 (fun x => snd (snd x)) p3))). 



(*Types used in all examples*)
Definition ExInputType := Times TInput TInput.
Definition ExOutputType := Times (Option_swi TOutput) (Option_swi TOutput).

Definition streamType := Stream ([TInput] + (([ExOutputType]))).

Definition InputRel : myrel ([TInput]). 
  refine (@MyRel _
            (fun l a => if l == \bot then a = DiskRead else False)
            (fun l a b => a = b) _ _ _ _).
  intros.
  done.
  intros.
  move: H0.
  case_if;last by [].
  move: H. rewrite /order.
  move/eqP: H0. intros. subst.
  rewrite lex0 in H. rewrite H. done.
  intros. subst. done.
Defined.

Definition OutputRel : myrel ([TOutput]).
  refine (@MyRel _
            (fun l a => if l == \bot  then a = Step else False)
            (fun l a b => a = b) _ _ _ _).
  intros.
  done.
  intros.
  move: H0.
  case_if;last by [].
  rewrite /order (eqP H0) lex0 in H.
  by rewrite H.

  by intros;subst.
Defined.

Definition Input_prod : myrel ([ExInputType]).
  apply: eqpair_LR;apply InputRel;apply InputRel.
Defined.

Definition Output_option : myrel ([Option TOutput]) := eqmaybe (fun l => l = \top) OutputRel.

Definition Output_option_prod : myrel ([ExOutputType]).
  apply eqpair. apply Output_option. apply Output_option.
  Defined.







(**Examples*)



(*Example 1: Interference
  Scheduler switches between p1 and p2 based on secret input (DiskRead)*)
Module Example1.
(*Process*)
Definition p1 := @out TInput TOutput Step.
Definition p2 := @out TInput TOutput Idle.
Definition process_pool := par_swiI false p1 p2.

Definition scheduler (p : Proc (Times Bool (Times TInput TInput)) (Times (Option_swi TOutput) (Option_swi TOutput))) :=
  @map _ (Times Bool (Times TInput TInput)) _ _ (fun (i : [TInput]) => (i == DiskRead,(i,i))) id p.

(*Trace*)
Definition newtraceF_simple (newtrace : streamType) := Cons (inl (DiskRead))
                                                               (Cons (inr (Some Step,None))
                                                                  (Cons (inl (DiskRead)) newtrace)).
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
Ltac rewr ::=  (try rewrite newtrace_simple_eq); rewrite /newtraceF_simple /process_pool /par_swiI /scheduler /p1 /p2.
Check process_pool.
Lemma simple_trace : trace newtrace_simple (scheduler process_pool).
Proof.
  pcofix CIH.
  rewr.
  bundle. left.
  bundle. left.
  bundle. right.
  swi_instans. eauto.
Qed.

(*NotSim*)
Example counterexample : NotSim \bot InputRel Output_option_prod newtrace_simple (scheduler process_pool).
Proof. 
  rewrite newtrace_simple_eq /newtraceF_simple.
  apply: NS2. instantiate (1:= (DiskRead)).
  rewrite /= eqxx. auto.

  intros. match_dd.

  apply: NS3. ssa. de x. subst.
  match_dd.
  
  apply: NS4. ssa. de o'. subst.
  match_dd.
Qed.  

(*Not NI*)
Example example_not_NI :  ~ NI InputRel Output_option_prod (scheduler process_pool).
Proof.
  rewrite /NI. ssa. intro.

  apply/toNotSim. apply/counterexample.
  apply/H. apply simple_trace.
Qed.
End Example1.

(*Example 2: Non-interference
 round-robin between p1 with low output and p2 with high output
 Both have low input*)
Module Example2.
Definition p1 := (@out TInput TOutput Step). (*high*)  
Definition p2 := (@out TInput TOutput Idle). (*low*)
Definition process_pool := par_swiI false p1 p2.
Definition scheduler {I O} (p : Proc (Times Bool (Times I I)) O) : Proc I O := @map _ (Times Bool (Times _ _)) _ _ (fun i => (true,(i,i))) id p.

Definition InputRelPublic : myrel ([TInput]) := publicRel TInput. 

Definition TraceF_specific := (@TraceF TInput (Times (Option TOutput) (Option TOutput))).
Lemma specific_monotone : monotone2 TraceF_specific.
  apply (@monotone_TraceF TInput (Times (Option TOutput) (Option TOutput))).
Qed.

Hint Resolve specific_monotone : paco.


Arguments NI : clear implicits.
(*Arguments NI I O [_] [_].*)
Example hl_lp_NI : @NI _ _ InputRelPublic Output_option_prod (scheduler process_pool).
Proof.
  rewrite /scheduler.
  eapply map_NI.
  eapply par_swiI_NI.
  apply out_NI.
  apply out_NI.
  instantiate (1:= (InputRelPublic)).
  instantiate (1:= (InputRelPublic)).  
  rewrite /f_NI. ssa.

  rewrite /f_PU. ssa.
  rewrite /f_NI. ssa.
  Unshelve. apply OutputRel. apply OutputRel.
Qed.
End Example2.

Print Hint *. 
(*Example 3*)
Module Example3.
  
Definition low_p := @out TInput TPublicOutput GetRequest.
Definition high_p := @out THandlerOutput TTypeSyscall Syscall. 

(*Handler is complicated because we need to do 2 things:
1) Switch what we output based on whether an input has happened since the last output
2) reset the state after the output has been performed

in sta, the state cannot be inspected in the making of the output, resetting the state therefore removes the information we would need to distinguish states.
Using the loop construct we can turn "on" the Notify output by receiving an input. Sending the Notify output will due to the loop construct, create a new input, tagged with inr, which resets the state
 *)
Definition handler := @map _ (Sum _ _) (Sum _ (Times Bool Unit)) THandlerOutput 
                        inl
                        (fun o => if o is inr (true,tt) then Notify else Nothing)
                        (@loop (Sum TInterrupt (Times Bool Unit))
                        (@map (Sum TInterrupt _) _ _ (Sum _ _) id (fun o => inr o)
                        ((@sta (Sum _ _) _ Bool
                           (fun i v => if i is inl _ then true else false)
                           (fun o v => v)
                           false
                           (@out (Times Bool _ ) Unit tt)
                        )))).

Definition InputType := (Times (Option_maybe TInput) (Times (Option_maybe THandlerOutput) (Option_maybe TInterrupt))).

Definition NInputType := Times Nat InputType.
Definition OutputType :=  (Times (Option_swi TPublicOutput) (Times (Option_swi TTypeSyscall) (Option_swi THandlerOutput))).

Definition IOType := Sum InputType OutputType. 

Definition process_pool := par_swiI3 0 (maybe low_p) (maybe high_p) (maybe handler).


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

(*Definition bad_scheduler := loop (@map _ _ (Times _ _) _ id snd (@sta _ _ state_type1 state_in1 (fun o v => inc_state1 v) (false,(0,0)) (@map (Times state_type1 _) (Times Nat _) _ _ (fun x => (to_schedule1 (fst x), snd x)) id process2))).*)

Definition outf : [IOType] -> [OutputType] :=  (fun x => match x with | inl _ => (None,(None,None)) | inr y => y end).

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
                (fun x => let n := to_schedule (fst x) in (*map *)
                          match snd x with
                          | inl i' => (n,i') (*inl = input*)
                          | inr (None,(None,Some h)) => (n,(None,(Some h,None))) (*inr = output from handler rerouted as input to high process *)
                          | inr _ => (n,(None,(None,None))) (*inr = output that is discarded, but n is used to ac*)
                          end)
                inr
                p
    )))).

(*schedules handler on hardware interrupt input*)
Definition bad_scheduler := @scheduler state_type1 state_in1 (fun _ v => inc_state1 v) (false,(0,0)) to_schedule1.

Definition full_process := bad_scheduler process_pool.

Definition ex3_stream_type := ([InputType] + [OutputType])%type.
Definition myTimerInt : ex3_stream_type := inl (None,(None,Some TimerInterrupt)).
Definition myDiskInt : ex3_stream_type := inl (None,(None,Some DiskInterrupt)).
Definition myGet  : ex3_stream_type := inr (Some GetRequest,(None,None)).
Definition mySys : ex3_stream_type := inr (None,(Some Syscall,None)).
Definition myNotify : ex3_stream_type := inr (None,(None,Some Notify)).

Definition ex3_streamF (s : Stream ex3_stream_type) := Cons myGet
                                                         (Cons myGet
                                                            (Cons mySys
                                                               (Cons mySys
                                                                  (Cons myTimerInt
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

Ltac rewr ::=  (try rewrite ex3_stream_eq); rewrite /par_swiI /bad_scheduler /process_pool /low_p  /ex3_streamF /bad_scheduler /process_pool /par_swiI3 /high_p /handler /sta_swi /scheduler.


Ltac reduce_twice := reduce_once;(try reduce_once);(try eapply Logic.eq_refl).
Example simple_trace : trace ex3_stream (bad_scheduler process_pool).
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
Qed.


Definition InputTypeRel : myrel [InputType] := to_rel InputType.

Definition OutputTypeRel : myrel [OutputType] := to_rel OutputType.

Ltac dd H := dependent destruction H.
(*got to here, probably eqmaybeT dis predicate is wrong?*)
Example counterexample : NotSim \bot InputTypeRel OutputTypeRel ex3_stream (bad_scheduler process_pool).
Proof.
  Admitted. (*outcomment proof because it is slow*)
(*
apply: NS2.
  instantiate (1:= (None,(None,(Some TimerInterrupt)))).
  ssa.
  move=>p'. rewr. ssa.
  match_dd.
  apply:NS4.
  ssa.
  match_dd.
Qed.  *)

Example example_not_NI : ~ @NI _ _ InputTypeRel OutputTypeRel (bad_scheduler process_pool).
Proof.
  rewrite /NI. ssa. intro.
  apply/toNotSim. apply/counterexample.
  apply/H. apply simple_trace.
Qed.

Coercion to_rel_locked : Ty >-> myrel.

Definition NI2 I O (p : Proc I O) := NI I O I O p.
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
Qed.

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

Lemma NI_add_L : forall I V O (p : Proc I (Times V O)),
    NI I (Times V O) (to_rel I) (eqpair_R (to_rel V) (to_rel O)) p ->
    NI I (Times V O) (to_rel I) (eqpair_LR (to_rel V) (to_rel O)) p.
Proof.
  intros. 
  apply/simulation_equiv.
  move/simulation_equiv : H.
  intros. apply/NI_swap_rel. 2:eauto.
  ssa.
Qed.

Lemma NI_add_R : forall I V O (p : Proc I (Times V O)),
    NI I (Times V O) (to_rel I) (eqpair (to_rel V) (to_rel O)) p ->
    NI I (Times V O) (to_rel I) (eqpair_R (to_rel V) (to_rel O)) p.
Proof.
  intros. 
  apply/simulation_equiv.
  move/simulation_equiv : H.
  intros. apply/NI_swap_rel. 2:eauto.
  ssa.
Qed.

Lemma SimulationF_I_imp : forall I O l (IRel IRel' : myrel [I]) (ORel : myrel [O]) R s p, (forall l x, dis IRel' l x -> dis IRel l x) -> (forall l x y, rel IRel l x y <-> rel IRel' l x y) -> SimulationF l IRel ORel R s p -> SimulationF l IRel' ORel R s p.
Proof.
  intros. inv H1. con;eauto.
  rewrite /Clause1. ssa. eauto.
  rewrite /Clause2. ssa. 
  rewrite /Clause3. ssa.
  move: H4. rewrite /Clause3. ssa. eapply H4 in H6;eauto. apply/H0. done.
Qed.


Lemma simulation_I_imp : forall I O (IRel IRel' : myrel [I]) (ORel : myrel [O]) p,
    (forall l x, dis IRel' l x -> dis IRel l x) -> (forall l x y, rel IRel l x y <-> rel IRel' l x y) -> NI I O IRel ORel p -> NI I O IRel' ORel p.
Proof.
  intros. 
  intros. rewrite /NI. intros. eapply H1 in H2.
  move: H2. instantiate (1:=l).
  apply:paco2_imp. apply monotone_SimulationF.
  intros. apply/SimulationF_I_imp. 3:eauto. eauto. eauto.
Qed.  

Lemma NI_I_remove_L : forall I V O (p : Proc (Times V I) O),
    NI (Times V I) O (eqpair_LR (to_rel V) (to_rel I)) (to_rel O) p ->
    NI (Times V I) O (eqpair_R (to_rel V) (to_rel I)) (to_rel O) p.
Proof.
  intros. apply/simulation_I_imp. 3:eauto.
  ssa. ssa.
Qed.


Lemma sta_NI2 : forall (I O V : Ty) (p : Proc (Times V I) O) f g v,
    fv_NI2 g->
    fv_NI2 f /\ f_EP2 f ->
    NI2 p ->    
    NI2 (sta f g v p).
Proof.
  intros. rewrite /NI2.
  ulock. simpl. apply/NI_add_L/NI_add_R.
  apply:sta_NI;eauto. rewrite /NI2 in H. ssa. apply/NI_I_remove_L. done.
  move: H. rewrite /NI2. ssa.
  rewrite /fv_NI;ssa.
Qed.


Lemma swi_NI2 : forall (I O : Ty) (p : Proc I (Times Bool O)) b,
    NI2 p ->
   (* (forall l, aware Bool true l \/ oblivious (Times Bool O) p l) ->*) (*remove this part, because (to_rel Bool) : myrel [Bool] is always aware*)
    NI2 (swi b p).
Proof.
intros. 
rewrite /NI2. ulock. simpl. 
apply/swi_NI. eauto.
ssa. left. rewrite /aware. ssa.
Qed.

Lemma maybe_NI2 : forall (I O :Ty) (p : Proc I O), NI2 p -> NI2 (maybe p).
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

Ltac rewr ::=  (try rewrite ex3_stream_eq); rewrite /par_swiI /bad_scheduler /process_pool /low_p  /ex3_streamF /bad_scheduler /process_pool /par_swiI3 /high_p /handler /sta_swi /scheduler /mitigator.

Hint Resolve InputTypeRel OutputTypeRel eqsum : rels.

(*Ltac NI_tac := (*rewrite /IOType /state_type2;*)(match goal with 
               | [ |- @NI _ _ _ _ (map _ _ _)] => apply: map_NI2
               | [ |- @NI _ _ _ _ (loop _)] => apply: loop_NI2
               | [ |- @NI _ _ _ _ (sta _ _ _ _)] => apply: sta_NI2
               | [ |- @NI _ _ _ _ (par _ _)] => apply: par_NI2
               | [ |- @NI _ _ _ _ (swi _ _)] => apply: swi_NI2
               | [ |- @NI _ _ _ _ (maybe _)] => apply: maybe_NI2
               | [ |- @NI _ _ _ _ (out _)] => apply: out_NI2
                                                 end);eauto with rels;try solve [ssa].*)


(*               | [ |- @NI _ _ _ _ (map _ _ _)] => apply: map_NI2
               | [ |- @NI _ _ _ _ (loop _)] => apply: loop_NI2
               | [ |- @NI _ _ _ _ (sta _ _ _ _)] => apply: sta_NI2
               | [ |- @NI _ _ _ _ (par _ _)] => apply: par_NI2
               | [ |- @NI _ _ _ _ (swi _ _)] => apply: swi_NI2
               | [ |- @NI _ _ _ _ (maybe _)] => apply: maybe_NI2
               | [ |- @NI _ _ _ _ (out _)] => apply: out_NI2
               end);eauto with rels;try solve [ssa].*)

(*overview over types
  InputType  = Times (Option TInput) (Times (Option THandlerOutput) (Option TInterrupt))
  OutputType = Times (Option TPublicOutput) (Times (Option TTypeSyscall) (Option THandlerOutput))
  IOType = Sum InputType OutputType
 *)
(*Lemma test_f_NI :  @f_NI InputType IOType InputTypeRel _ (@inl [InputType] (option PublicOutput * (option TypeSyscall * option HandlerOutput))).*)

Lemma to_rel_eq (A : Ty) l x y  : rel (# A) l x y -> x = y.
Proof. ulock.
  move: A x y. elim;ssa.
  de x. de y. f_equal;eauto.
  de x. de y. f_equal. eauto. de y. f_equal. eauto.
Qed.

Definition to_rel_eq_IOType := @to_rel_eq IOType.
Definition to_rel_eq_state_type2 := @to_rel_eq state_type2.


Lemma eq_to_rel (A : Ty) l x y  : x = y -> rel (# A) l x y.
Proof.
  move=>->. eauto.
Qed.

Definition eq_to_rel_OutputType := @eq_to_rel OutputType.

Lemma f_NI_eq A B f: f_NI #A #B f.
  rewrite /f_NI. ssa. apply/eq_to_rel.
  apply to_rel_eq in H. subst. done.
Qed.

Lemma f_NI_id (A : Ty) B : @f_NI A A B B id.
  rewrite /f_NI. done.
Qed.

Lemma f_PU_id (A : Ty) B : @f_PU A A B B id.
  rewrite /f_PU. done.
Qed.  
Hint Resolve f_NI_eq f_NI_id f_PU_id.

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

Ltac clean_rel := repeat match goal with | H : rel (to_rel_locked ?T) _ _ _ |- _  => apply (@to_rel_eq T) in H | |- rel (to_rel_locked ?T) _ _ _ => apply (@eq_to_rel T); subst end.
Ltac NI_tac := first [ apply:map_NI2 | apply:loop_NI2 | apply:sta_NI2 | apply:par_NI2 | apply:swi_NI2 | apply:maybe_NI2 | apply:out_NI2 ];ssa;rewrite /outf /f_NI2 /f_NI_PU2 /fv_NI2 /fv_NI /f_PU /f_NI /f_EP2;ssa;
               try solve [ intros;clean_rel;ssa | eauto with mitdb].



Theorem mitigator_NI : NI2 (mitigator process_pool).
Proof.
  NI_tac.
  NI_tac.
  NI_tac.
  NI_tac.
  NI_tac.
  ssa.
  move: H. ulock. ssa. right. de i. de s. de p0. de o. right. de p0. de o.
  de p0. de o. de p0. de o. de o0.

  NI_tac.
  NI_tac.

  apply:sta_NI2. admit. con. rewrite /fv_NI2. ssa. by clean_rel.
  rewrite /f_EP2. ssa.
  NI_tac.
  move: H. ulock. ssa. de H. de i. de p. de o. de H. de p. de o. de H.
 de H.  rewrite /fv_NI2. ssa. by clean_rel.
  intros. by  clean_rel.

  
  rewrite /f_NI_PU2. con. rewrite /f_NI. intros. by clean_rel.
  rewrite /fv_NI2. intros. by 

  test.
  apply (@to_rel_eq IOType) in H.
  apply (
  unshelve NI_tac.

  NI_tac. con;eauto with rels. eauto.
  con. eauto with rels.
  rewrite /f_NI. Print f_NI.
  eauto with rels. eauto with rels.
  all:ssa. 2: { rewrite /f_NI. intros. have: (eqsum InputType OutputType InputTypeRel OutputTypeRel)
                eauto. apply rel_eq. ssa. de i. de i'. de i'. de i. de i'. de i'. de i. de i'. de i'. } 

  unshelve NI_tac.

  un
    NI_tac. 3: NI_tac.  



    eauto with rels. 
(*    apply publicRel;ssa.
    ssa. 
    rewrite /f_NI. ssa. subst. de i'. de s.*)
Check sta_NI.
    apply: sta_NI.
    unshelve NI_tac.
  - Unshelve 1.
  NI_tac.
  NI_tac.
  NI_tac.
  do 10 (try NI_tac).
  rewrite /
  unshelve apply: map_NI.

  Ltac mytest := rewrite /IOType;eauto with rels.
  mytest. mytest.
  un
  apply eqsum; eauto with rels.
  NI_tac. instantiate (2:=eqsum _ _ _ _);simpl. 
2: { Set Printing Implicit. rewrite /f_NI.
2: { rewrite /f_NI. intros.
do 2 (try NI_tac).
NI_tac.
NI_tac.



(*good_scheduler not used currently, should it be removed?*)
(*
Definition myvT2 := (Times Nat Nat).
Definition inc_myv2 (v : [myvT2]) := let: ((c,n)) := v in if c == 0 then (c+1,n) else (0,(n+1)%%3).
Definition myv_to_n2 (v: [myvT2]) : nat := let: (c,n) := v in n.

(*Treats handler as the third process, round-robin scheduling between the three*)
Definition good_scheduler := scheduler myvT2 (fun _ v => v) (fun _ v => inc_myv2 v) ((0,0)) myv_to_n2.
 *)
End Example3.
