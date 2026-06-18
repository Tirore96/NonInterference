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

       












Lemma out_NI : forall I O (IRel : myrel [I]) (ORel : myrel [O]) (o : [O]), NI IRel ORel (out o).
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
Lemma sta_proj : forall (I O V : Ty) (p : Proc (Times V I) O) (VRel : myrel [V]) (ORel : myrel [O]) (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) l v ts,
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
Lemma sta_proj_insert : forall (I O V : Ty) (p : Proc (Times V I) O) (VRel : myrel [V]) (ORel : myrel [O]) (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) l v n i t,
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

Lemma NI_reduceI : forall I O (IRel : myrel [I]) (ORel : myrel [O]) (p p' : Proc I O) i,
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

Lemma NI_reduceO : forall I O (IRel : myrel [I]) (ORel : myrel [O]) (p p' : Proc I O) o,
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
Fixpoint lthread (V I O : Ty) (VRel : myrel [V]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) (l : level) (v : [V]) (L : seq ([Times V I] + [Times V O])) : Prop :=
  match L with
  | nil => True
  | inl wi :: L' => rel VRel l (fst wi) (f (snd wi) v) /\ lthread VRel f g l (f (snd wi) v) L'
  | inr wo :: L' => rel VRel l (fst wo) (g (snd wo) v) /\ lthread VRel f g l (g (snd wo) v) L'
  end.

Lemma lthread_stable : forall (V I O : Ty) (VRel : myrel [V]) (IRel : myrel [I]) (ORel : myrel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l L v v',
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
Lemma sta_conv : forall (I O V : Ty) (VRel : myrel [V]) (IRel : myrel [I]) (ORel : myrel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l L (p : Proc (Times V I) O) v,
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
Lemma sta_proj_lthread : forall (I O V : Ty) (p : Proc (Times V I) O) (VRel : myrel [V]) (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) l v ts,
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
Lemma lthread_swap : forall (V I O : Ty) (VRel : myrel [V]) (IRel : myrel [I]) (ORel : myrel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l T'' n w i i' v,
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

Lemma lthread_insert_dis : forall (V I O : Ty) (VRel : myrel [V]) (IRel : myrel [I]) (ORel : myrel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l T n i v,
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

Lemma lthread_remove_dis : forall (V I O : Ty) (VRel : myrel [V]) (IRel : myrel [I]) (ORel : myrel [O]) (f : [I]->[V]->[V]) (g : [O]->[V]->[V]) l T'' n w i v,
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
Lemma sta_NI : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O]),
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

Inductive SwiTrace (I O : Ty) (ORel : myrel [O]) (BRel : myrel [Bool]) (l : level) : bool -> seq ([Times Bool I] + [Option O]) -> seq ([I] + [Times Bool O]) -> Prop :=
| ST0 b : SwiTrace ORel BRel l b nil nil
| ST1 b b' i t_swi t_p : SwiTrace ORel BRel l (xor b b') t_swi t_p -> SwiTrace ORel BRel l b (inl (b', i) :: t_swi) (inl i :: t_p)
| ST2_false o t_swi t_p : rel (eqmaybe_swi ORel BRel) l None o -> SwiTrace ORel BRel l false t_swi t_p -> SwiTrace ORel BRel l false (inr o :: t_swi) t_p
| ST2_true b_out o o_obs t_swi t_p : rel (eqmaybe_swi ORel BRel) l (Some o) o_obs -> SwiTrace ORel BRel l (negb b_out) t_swi t_p -> SwiTrace ORel BRel l true (inr o_obs :: t_swi) (inr (b_out, o) :: t_p).

Lemma swi_trace : forall (I O : Ty) (p : Proc I (Times Bool O)) (ORel : myrel [O]) (BRel : myrel [Bool]) l b t,
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

Lemma swi_trace_insert : forall (I O : Ty) (ORel : myrel [O]) (BRel : myrel [Bool]) l b t t' n (i : bool * [I]),
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

Lemma swi_trace_insert_conv : forall (I O : Ty) (ORel : myrel [O]) (BRel : myrel [Bool]) l b t t_p n (i : bool * [I]),
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

Lemma swi_trace_swap : forall (I O : Ty) (ORel : myrel [O]) (BRel : myrel [Bool]) l b t t_p n (i i' : bool * [I]),
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

Lemma swi_trace_remove : forall (I O : Ty) (ORel : myrel [O]) (BRel : myrel [Bool]) l b t t_p n (i : bool * [I]),
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

Lemma swi_conv : forall (I O : Ty) (p : Proc I (Times Bool O)) (ORel : myrel [O]) (BRel : myrel [Bool]) l b t t_p,
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









Theorem swi_NI : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (BRel : myrel [Bool]) p b,
(forall l, aware BRel true l \/  oblivious (eqpair_R BRel ORel) p l ) -> NI IRel (eqpair_LR BRel ORel) p ->                                
NI (eqpair_LR BRel IRel) (eqmaybe_swi ORel BRel) (swi b p).
Admitted.




Theorem maybe_NI : forall (I O :Ty) (IRel : myrel [I]) (ORel : myrel [O]) p, NI IRel ORel p -> NI (eqmaybe_false IRel) ORel (maybe p).
Admitted.

Theorem loop_NI : forall (I : Ty) (IRel : myrel [I]) p, NI IRel IRel p -> NI IRel IRel (loop p).
Admitted.

Theorem par_NI : forall (I O1 O2 : Ty) (IRel : myrel [I]) (ORel1 : myrel [O1]) (ORel2 : myrel [O2]) p1 p2,
    NI IRel ORel1 p1 -> NI IRel ORel2 p2 -> NI IRel (eqpair ORel1 ORel2) (par p1 p2).
Admitted.


