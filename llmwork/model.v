Global Set Warnings "-all".
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
Require Import Stdlib.Classes.DecidableClass.

Import Order.TTheory.
Open Scope order_scope.

Set Automatic Obligations.
Fail Next Obligation.

(*Before*)
(*Parameter (level : tbLatticeType (Order.Disp tt tt)).*)

(*Just for now*)
Definition level := bool.

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
Inductive Interrupt := DiskInterrupt | TimerInterrupt.
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
                 | Option : Ty -> Ty | Sum : Ty -> Ty -> Ty | TInput | TOutput | TTypeSyscall | Unit | Unit1 | Unit2 |  TInterrupt | THandlerOutput |  TPublicOutput | TPublicInput. 

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
  | Unit | Unit1 | Unit2 => unit                     
  | TInterrupt => Interrupt
  | THandlerOutput => HandlerOutput
  | TPublicOutput => PublicOutput
  | TPublicInput => PublicInput                       
  end.
Notation "[ i ]" := (interp i).



(*Record Inv (I I' : Ty) := mkInv {
  inv_fn :> [I] -> [I'];
  inv_pf : forall o : [I'], exists i : [I], inv_fn i = o
}.*)

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
(*Derive NoConfusion for Proc.
Derive NoConfusionHom for Proc.
Derive Signature for Proc.*)

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

(*Create HintDb omitdb.
Hint Resolve reduce_mapI reduce_staI reduce_swiI reduce_maybeI reduce_maybeI2 reduce_parI reduce_loopI : omitdb.*)

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


Inductive Trace (I O : Ty) (ORel : myrel [O]) (l : level) : list ([I] + [O]) -> Proc I O -> Prop :=
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

Definition NI_l (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (l : level) (p : Proc I O) : Prop :=
  (forall t i i' n, rel IRel l i i' -> Trace ORel l (insert n (inl i) t) p -> Trace ORel l (insert n (inl i') t) p) /\
  (forall t i n, dis IRel l i -> Trace ORel l t p -> Trace ORel l (insert n (inl i) t) p) /\
  (forall t i n, dis IRel l i -> Trace ORel l (insert n (inl i) t) p -> Trace ORel l t p).


Definition NI (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (p : Proc I O) := forall l, NI_l IRel ORel l p.


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

Definition eqpair_REQ {I O : Ty} (def : [I]) (ORel : myrel [O]) : myrel ([Times I O]).
  refine (@MyRel _ 
            (fun (l : level) io => fst io = def /\ dis ORel l (snd io))
            (fun l io1 io2 => rel (publicRel _) l (fst io1) (fst io2) /\ rel ORel l (snd io1) (snd io2) \/ fst io1 = fst io2 /\ dis ORel l (snd io1) /\ dis ORel l (snd io2))
            _
            _
            _
            _).
  - move=> l. 
    con.  destruct ORel. simpl. con.
    move: (equiv0 l). case. eauto.
  - rewrite /Symmetric. intros. destruct H. destruct ORel. simpl.
    ssa. left.
    move: (equiv0 l). case.
    move => _ Hsym _. con.  symmetry. done.
    eauto.
    ssa. 

  - destruct ORel. simpl. intro. intros.

    de H. de H0. left. ssa.
    move: (equiv0 l). case. move=> _ _ Htrans. rewrite H H0. done.
    move: (equiv0 l). case. move=> Hrefl0 _ Htrans0. eauto.
    move: (equiv0 l). case. move=> Hrefl0 _ Htrans0. eauto.    
    left. con. rewrite H H0. done. apply/Htrans0. eauto.
    apply i. done. done.
    destruct H0. ssa. left. con.
    move: (equiv0 l). case. move=> Hrefl _ Htrans. by rewrite H H0.

    move: (equiv0 l). case. move=> Hrefl0 _ Htrans0. 
    apply/Htrans0. 2:eauto.
    apply i. done. done. ssa.
    rewrite H H0. ssa.

  - intros. de H0.
    left. ssa.
    de ORel;eauto. 
    left. ssa. de ORel. eapply r.
     eauto. apply i. done. done.
  - intros. de ORel;eauto. de ORel;eauto.

  - intros. 
    intros. con. ssa. left. ssa. rewrite H -H1. done. apply i. done. done.
    ssa. destruct H1. ssa. rewrite -H1 H. done. ssa. rewrite -H1 H. done.
    destruct H1. ssa. apply/i. 2:eauto. done.
    ssa.
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
    de z. de y. de y.
    move: (equiv1 l). case. move=> _ _ Htrans. apply/Htrans. eauto. eauto.
    intros. de a0. de a1. de IRel;eauto. de IRel;eauto.
    de ORel;eauto.
    de a1. eauto.
    done.
    intros. con. done.
    de a0.
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

Definition aware (V : Ty) (VRel : myrel [V]) (v : [V]) : levelPred
  := fun l => (forall v', rel VRel l v v' -> v = v' /\ ~ dis VRel l v').

Definition Option_presP_swi (BRel : myrel [Bool]) : presP (fun l => aware BRel true l).
  rewrite /presP. intros. destruct BRel. move: H0. rewrite /aware. ssa.
  have: rel0 x0 true v'. eauto. move/H0. ssa.
  have: rel0 x0 true v'. eauto. move/H0. ssa. eauto.
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

Definition eqmaybe_swi {V : Ty} (VRel : myrel [V]) (BRel : myrel [Bool]) : myrel ([Option V]).
  apply:eqmaybe_aux. apply VRel. apply: Option_presP_swi. apply BRel.
Defined. 

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
      | Sum t0 t1 => eqsum_LR (to_rel t0) (to_rel t1)
      | Bool => boolRel
    | ty' => publicRel ty'
    end.

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


Definition f_NI {I O :Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O]) := forall (l : level) (i i' : [I]), rel IRel l i i' -> rel ORel l (f i) (f i').
Definition f_PU {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O]) := forall l (i : [I]), dis IRel l i -> dis ORel l (f i).
Definition f_NI_PU {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O])  := f_NI IRel ORel f /\ f_PU IRel ORel f.
Definition fv_NI (I O V: Ty) (IRel : myrel [I]) (ORel : myrel [O]) (VRel : myrel [V])  (f : [I] -> [V] -> [O]) := forall l (i i' : [I]), rel IRel l i i' -> forall (v v' : [V]), rel VRel l v v' -> rel ORel l (f i v) (f i' v').
Definition f_EP (I V: Ty) (IRel : myrel [I]) (VRel : myrel [V]) (f : [I] -> [V] -> [V]) := forall l i, dis IRel l i -> forall v, rel VRel l (f i v) v. (*equivalence preserving*)


 (*fixed typo in paper: In conclusion, replaced I with Bool * I  *)
Lemma rel_eqpair : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, rel (eqpair ARel BRel) l a b -> rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2.
Proof.
  ssa.
Qed.

Lemma rel_eqpair2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l a b, 
    rel ARel l a.1 b.1 /\ rel BRel l a.2 b.2 -> rel (eqpair ARel BRel) l a b.
Proof.
  ssa.
Qed.

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












Lemma f_NI_id (A : Ty) B : @f_NI A A B B id.
  rewrite /f_NI. done.
Qed.

Lemma f_PU_id (A : Ty) B : @f_PU A A B B id.
  rewrite /f_PU. done.
Qed.  
Hint Resolve (*f_NI_eq*) f_NI_id f_PU_id.

Ltac mrw := rewrite /f_NI /f_PU /fv_NI /f_EP.




Lemma f_NI_snd_eqpair : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]), f_NI (eqpair ARel BRel) BRel snd. 
Proof.
mrw. ssa.
Qed.

Lemma f_NI_snd_eqpair_LR : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]), f_NI (eqpair_LR ARel BRel) BRel snd. 
Proof.
mrw. ssa.
Qed.

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

Definition pair_rewr := (simp_pair1,simp_pair2).

Lemma rel_eqmaybe : forall (A : Ty) (ARel : myrel [A]) l x y, rel ARel l x y -> rel (eqmaybe ARel) l (Some x) (Some y).
Proof. ssa.
Qed.





  Lemma rel_eqpair_OR : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l x0 x1 y0 y1,
      rel (eqpair_OR ARel BRel) l (x0,x1) (y0,y1) -> rel ARel l x0 y0 /\ rel BRel l x1 y1 \/ (dis ARel l x0 \/ dis BRel l x1) /\ (dis ARel l y0 \/ dis BRel l y1).  
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

  Lemma rel_eqmaybe_swi2 : forall (A : Ty) (ARel : myrel [A]) (BRel : myrel [Bool]) l x y, rel (eqmaybe_swi ARel BRel) l x y -> (exists x' y', x = Some x' /\ y = Some y' /\ rel ARel l x' y') \/
                                                                                               (x = None /\ y = None) \/ (eqmaybe_dis (aware BRel true) ARel l x /\ eqmaybe_dis (aware BRel true) ARel l y).
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

  Definition is_inl (A B : Set) (x : A + B) := if x is inl _ then true else false.
  Definition is_inr (A B : Set) (x : A + B) := if x is inr _ then true else false.

  Lemma dis_eqsum_LR2 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l b, dis BRel l b -> dis (eqsum_LR ARel BRel) l (inr b).
  Proof. intros. ssa.
  Qed.
    
  Lemma aware_public : aware (publicRel Bool) true \bot.
  Proof. rewrite /aware. ssa.
  Qed.
  Hint Resolve aware_public.
