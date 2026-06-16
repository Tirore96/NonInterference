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
(*Hint Resolve reduce_mapO reduce_staO reduce_swiO reduce_swiO2 reduce_maybeO reduce_parO reduce_loopO : omitdb.*)

(*Inductive Trace (I O : Ty) (ORel : myrel [O]) (l : level) : list ([I] + [O]) -> Proc I O -> Prop :=
| TR0 p : Trace ORel l nil p
| TR1 p a t : Trace ORel l t p -> Trace ORel l (a::t) p
| TR1 p a t i i' : rel  -> Trace ORel (inl i) t p -> Trace ORel l ((inl i')::t) p                                                        
| TR1 p i p' t : reduceI p i p' -> Trace ORel l t p' -> Trace ORel l (inl i::t) p
| TR2 p o' o p' t : reduceO p o' p' -> rel ORel l o' o -> Trace ORel l t p' -> Trace ORel l (inr o::t) p.
Hint Constructors Trace.*)


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

(*Fixpoint swap (A : Set) (n : nat) (a : A) (l : seq A) :=
  match n with
  | 0 => if l is a'::l' then a::l' else nil
  | n'.+1 => if l is a'::l' then a'::(swap n' a l') else nil
end.*)    

Definition NI_l (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (l : level) (p : Proc I O) : Prop :=
  (forall t i i' n, rel IRel l i i' -> Trace ORel l (insert n (inl i) t) p -> Trace ORel l (insert n (inl i') t) p) /\
  (forall t i n, dis IRel l i -> Trace ORel l t p -> Trace ORel l (insert n (inl i) t) p) /\
  (forall t i n, dis IRel l i -> Trace ORel l t p -> Trace ORel l (remove n t) p).


Definition NI (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) (p : Proc I O) := forall l, NI_l IRel ORel l p.

(*Variant TraceF {I O : Ty} (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O -> Prop :=
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
  intros. intro. ssa. inv IN; eauto. all: econstructor; eauto.
Qed.
Hint Resolve MapSF_monotone2 : paco.

Definition MapS  (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) s s' := paco2 (@MapSF I I' O O' f g) bot2 s s'.

Definition MapRel (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) s p := exists s', MapS f g s' s /\ trace s' p.*)



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


(*Definition Clause1 (I O : Ty) (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
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

Definition simulation {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) l s p := paco2 (@SimulationF I O l IRel ORel) bot2 s p.*)
(*Definition NI (I O :Ty) (IRel : myrel [I]) (ORel : myrel [O])  (p : Proc I O) := forall l s, trace s p -> simulation IRel ORel l s p.*)

(*Check paco2.

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
Qed.  *)

(*Lemma SimulationF_imp : forall I O l (IRel : myrel [I]) (ORel : myrel [O]) R s p, SimulationF l IRel ORel R s p -> SimulationF l IRel (toPublicRel ORel) R s p.
Proof.
  intros. inv H. con;eauto.
Qed.

Lemma SimulationF_imp2 : forall I O l (IRel : myrel [I]) (ORel : myrel [O]) R s p, SimulationF l IRel (toPublicRel ORel) R s p -> SimulationF l IRel ORel R s p.
Proof.
  intros. inv H. con;eauto.
Qed.*)



(*Lemma simulation_equiv : forall I O (IRel : myrel [I]) (ORel : myrel [O]) p, NI IRel ORel p <-> NI IRel (toPublicRel ORel) p.
Proof.
  intros. split.
  intros. move: H. rewrite /NI /NI_l. intros.
  Admitted.*)
(*  intros.
  ssa.
  eapply H in H0.
  move: H0. instantiate (1:=l).
  apply:paco2_imp. apply monotone_SimulationF.
  intros. apply/SimulationF_imp. done.

  intros. rewrite /NI. intros. eapply H in H0.
  move: H0. instantiate (1:=l).
  apply:paco2_imp. apply monotone_SimulationF.
  intros. apply/SimulationF_imp2. eauto.
Qed.  *)


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

(*Definition to_rel_locked := to_rel.

Notation "# A" := (to_rel_locked A)(at level 5).
Lemma to_rel_unlock : to_rel_locked = to_rel. done.
Qed.
Opaque to_rel_locked.
Ltac ulock := rewrite to_rel_unlock.*)

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



(*  Lemma toNotSim : forall {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) s (p : Proc I O), NotSim l IRel ORel s p -> ~simulation IRel ORel l s p.
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
Qed.*)

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

(*Ltac appTrace := apply: traceI || apply: traceO.*)


(*Ltac bundle :=
  (pfold;
  first [ appTrace | rewr;appTrace ];
   first (do ? reduce_tac));controlled_eauto;simpl.

Ltac bundle_v :=
  (pfold;
  first [ appTrace | rewr;appTrace ];
  first (do ? reduce_tac_v));simpl;try econ.*)




Definition f_NI {I O :Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O]) := forall (l : level) (i i' : [I]), rel IRel l i i' -> rel ORel l (f i) (f i').
Definition f_PU {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O]) := forall l (i : [I]), dis IRel l i -> dis ORel l (f i).
Definition f_NI_PU {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O])  := f_NI IRel ORel f /\ f_PU IRel ORel f.
Definition fv_NI (I O V: Ty) (IRel : myrel [I]) (ORel : myrel [O]) (VRel : myrel [V])  (f : [I] -> [V] -> [O]) := forall l (i i' : [I]), rel IRel l i i' -> forall (v v' : [V]), rel VRel l v v' -> rel ORel l (f i v) (f i' v').
Definition f_EP (I V: Ty) (IRel : myrel [I]) (VRel : myrel [V]) (f : [I] -> [V] -> [V]) := forall l i, dis IRel l i -> forall v, rel VRel l (f i v) v. (*equivalence preserving*)

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

  ssa. clear H. elim: t n H0.
  auto.
  ssa. de n.

  ssa. de n. inv H0. match_dd. done. match_dd. done.
  inv H0. econ. eauto. match_dd. eauto.
  econ. eauto. done. match_dd. eauto.
Qed.  

(*Variant forall_gen {A : Type} (P : A -> Set)  (R : Stream A -> Prop)  : Stream A -> Prop :=
| FEE_cons x s : P x -> R s -> forall_gen P R (Cons x s).

Lemma forall_gen_mon (A : Type) (P : A -> Set)  : monotone1 (forall_gen P). 
Proof. 
move => x. intros. induction IN. constructor; auto.
Qed. 

Hint Resolve forall_gen_mon : paco. 
Definition ForallC {A : Type} (P : A -> Set) s := paco1 (forall_gen P) bot1 s.

Definition map_pred {I I' O O' : Ty} (g : [O] -> [O']) (o' : [I] + [O']) := { o : ([I] + [O]) &  match o',o with | inr oo',inr oo => g oo = oo' | _,_ => True end}.

Lemma trace_map : forall (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (s : Stream ([I] + [O'])) s (p : Proc I' O), trace s (map f g p) ->
                                                                                                                           ForallC (@map_pred I I' O O' g) s.
  move=>  I I' O O' f g s. pcofix CIH.
  intros.
  punfold H0. inv H0;match_dd;pc. pfold. con. ssa. con. eauto. con. eauto.
  pfold. con. rewrite /map_pred. exists (inr o). done. eauto.
Qed.

Definition trace_test (A B : Ty) (p : Proc A B) : { Stream ([A] + [B]). 
  elim: p.
  intros. cofix CIH. apply Cons. apply (inr i). apply CIH.
  admit. (*if the rest work, we come back here and add invertible condition on function in map constructor*)
  intros. move: H. cofix CIH. case.
  case. simpl. case. intros. apply Cons.
  left. apply b. apply CIH. apply s.
  intros. apply Cons. right. simpl. con. auto. auto. apply CIH. apply s.
  intros. move: H. cofix CIH. case. simpl. case.
  intros. apply Cons. left. con. apply b. apply a.
  apply CIH. simpl. apply s.
  case. intros. apply Cons. right. 
  apply CIH. app


  
Lemma trace_inhabited : forall (A B : Ty) (p : Proc A B), exists s, s p.

Lemma reduceI_trace : forall (A B : Ty) (p : Proc A B) (i : [A]) p', reduceI p i p' -> exists s, trace (Cons (inl i) s) p.
Proof.*)

Definition myrel_out (A B : Ty) (f : [A] -> [B]) (BRel : myrel [B]) : myrel [A].
  destruct BRel.
  refine (@MyRel _
            (fun l b => ((dis0 l) \o f) b)
            (fun l v1 v2 => rel0 l (f v1) (f v2))
            _
            _
            _
            _).
  ssa. destruct (equiv0 l). con. ssa. ssa.
  intro. intros. eauto.
  eauto.
  ssa. eauto.
  eauto.
Defined.

Inductive MapTrace (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (ORel : myrel [O']) (l : level) : seq ([I] + [O']) -> seq ([I'] + [O]) -> Prop  :=
| MT0 : MapTrace f g ORel l nil nil
| MT1 i t t' : (*reduceI p (f i) p' -> *) MapTrace f g ORel l t t' -> MapTrace f g ORel l ((inl i)::t) ((inl (f i))::t')
| MT2 o o' t t' : rel ORel l (g o) o' -> MapTrace f g ORel l t t' -> MapTrace f g ORel l ((inr o')::t) ((inr o)::t').

(*Lemma MapTraceP1 (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (ORel : myrel [O']) (l : level) (p : Proc I' O) t t':
  MapTrace f g ORel l t t' -> Trace ORel l t (map f g p).
Proof.
  elim. ssa. ssa. econ. eauto. eauto.
  ssa. econ. eauto. done. done.
Qed.

Lemma MapTraceP2 (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (ORel : myrel [O']) (l : level) (p : Proc I' O) t t':
  MapTrace f g ORel l p t t' -> Trace (publicRel _) l t' p.
Proof.
  elim. ssa. ssa. econ. eauto. eauto.
  ssa. econ. eauto. done. done.
Qed.

Lemma MapTraceP (I I' O O' : Ty) (f : [I] -> [I']) (g : [O] -> [O']) (ORel : myrel [O']) (l : level) (p : Proc I' O) t t':
   MapTrace f g ORel l p t t' -> Trace ORel l t (map f g p) /\ Trace (publicRel _) l t' p.
Proof.
  intros. apply MapTraceP1 in H as H'. apply MapTraceP2 in H. ssa.
Qed.*)
  
(*Lemma map_trace : forall (I I' O O' : Ty) (p : Proc I' O) (ORel : myrel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t,
    Trace ORel l t (map f g p) -> exists t', forall ORel', Trace ORel' l t' p /\ MapTrace f g ORel l p t t'.
Proof.
  intros. elim: t p H. ssa. exists nil. ssa. con.
  ssa. inv H0. match_dd. eapply H in H5. ssa.
  econ. intros.
  move: (H1 ORel'). clear H1. intros. con. destruct H1. 
  instantiate (1:= (inl (f i))::_). econ. eauto. eauto. econ. eauto. ssa.

  match_dd.
  apply H in H6. ssa.
  econ. intros.
  move: (H1 ORel'). case. intros. con.
  instantiate (1:= cons (inr _) _). econ. eauto.
  inv H0.
  apply H1 in H2 as H2'. destruct H2'.
  con. 2: {  econ. eauto. eauto. eauto. }  econ. eauto. done. done.
Qed. *)

Lemma trace_ORel : forall (I O : Ty) (p : Proc I O) (ORel ORel' : myrel [O]) t l, (forall x y, rel ORel l x y -> rel ORel' l x y) -> Trace ORel l t p ->  Trace ORel' l t p.
Proof.
  intros. elim: H0. ssa. ssa. econ. eauto. eauto.
  ssa. econ. eauto. eauto. done.
Qed.

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

Lemma map_trace_cons : forall (I I' O O' : Ty) (ORel' : myrel [O']) (f : [I] -> [I']) (g : [O] -> [O']) l t t' x y,
    MapTrace f g ORel' l (x::t) (y::t') -> MapTrace f g ORel' l t t'.
Proof.
  intros. elim : t t' H;ssa. inv H. inv H1. done. inv H5. done.
  inv H0. inv H2. econ. eauto. econ. done. done.
  inv H6. econ. done. econ. done. done.
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


  move: (H2 l). case=>_ [] _ HH. clear H2.
  intros.
  apply map_trace in H3. ssa.
  move: (H3 ORel).  ssa.
  eapply H0 in H2.
  eapply HH in H2. 2:eauto.
  move: H2. instantiate (1:= n).
  clear H4. clear HH H3.
  move: H5 p.
  move/map_trace_remove3.
  move/(_ n). elim. ssa.
  ssa. inv H4. econ. econ. eauto. eauto. eauto. 
  ssa. inv H5. econ. econ. eauto. eauto. eauto. eauto.
Qed.

    

Lemma sta_NI : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O]),
    fv_NI ORel VRel VRel g -> fv_NI IRel VRel VRel f -> f_EP IRel VRel f ->
    NI (eqpair_R VRel IRel) ORel p ->
    NI IRel (eqpair VRel ORel) (sta f g v p).
Admitted.


 (*fixed typo in paper: In conclusion, replaced I with Bool * I  *)  
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
    @NI _ _ IRel ORel R ->
    @NI _ _ IRel' ORel R.
Proof.
  intros. 
  intros. rewrite /NI. intros. eapply H1 in H2.
  move: H2. instantiate (1:=l).
  apply:paco2_imp. apply monotone_SimulationF.
  intros. apply/SimulationF_I_imp. 3:eauto. eauto. eauto.
Qed.


Lemma SimulationF_O_imp : forall I O l (IRel : myrel [I]) (ORel ORel' : myrel [O]) R s p,
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
    (forall l x y, rel ORel l x y -> rel ORel' l x y) ->
    @NI _ _ IRel ORel R ->
    @NI _ _ IRel ORel' R.
Proof.
  intros. 
  intros. rewrite /NI. intros. eapply H0 in H1.
  move: H1. instantiate (1:=l).
  apply:paco2_imp. apply monotone_SimulationF.
  intros. apply/SimulationF_O_imp. 2:eauto. eauto. 
Qed.





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

Lemma public_NI : forall (A B : Ty) (p : Proc A B) BRel, (forall x y l, rel BRel l x y -> x = y) -> @NI _ _ (publicRel _) BRel p.
Proof.
  intros. rewrite /NI. intros. apply/public_sim2;eauto.
Qed.



Lemma f_NI_id (A : Ty) B : @f_NI A A B B id.
  rewrite /f_NI. done.
Qed.

Lemma f_PU_id (A : Ty) B : @f_PU A A B B id.
  rewrite /f_PU. done.
Qed.  
Hint Resolve (*f_NI_eq*) f_NI_id f_PU_id.

Ltac mrw := rewrite /f_NI /f_PU /fv_NI /f_EP.

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

Lemma rel_eqmaybe : forall (A : Ty) (ARel : myrel [A]) l x y, rel ARel l x y -> rel (eqmaybe ARel) l (Some x) (Some y).
Proof. ssa.
Qed.



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

       
Definition pair_rewr := (simp_pair1,simp_pair2).

Definition inl_some {A B : Set} (x : A + B) := if x is inl x' then Some x' else None.
Definition inr_some {A B : Set} (x : A + B) := if x is inr x' then Some x' else None.
Definition option_inl_some {A B : Set} (x : option (A + B)) := if x is Some (inl x') then Some x' else None.
Definition inr_inl_some {A B C : Set} (x : A + (B + C)) := if x is inr (inl x') then Some x' else None.
Definition inr_inr_some {A B C : Set} (x : A + (B + C)) := if x is inr (inr x') then Some x' else None.
Definition is_none (A : Set) (x : option A) := if x is None then true else false.
Definition is_some (A : Set) (x : option A) := if x is Some _ then true else false.
Definition some_inl (A B : Set) (x : option (A + B)) : option A := if x is Some (inl x') then Some x' else None.

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
Definition times_Option_n (n : nat) (f : nat -> Ty) := times_N n (Option \o f).

(*Example*)
Definition my_f_I := fun (n : nat) => match n with
                                      | 0 => TInterrupt (*handler*)
                                      | 1 => THandlerOutput (*private*)
                                      | 2 => Unit (*public*)
                                      | 3 => Sum TInterrupt THandlerOutput (*scheduler*)
                                      | _ => Unit
                                      end.

Definition my_f_O := fun (n : nat) => match n with
                                      | 0 => THandlerOutput
                                      | 1 => TTypeSyscall
                                      | 2 => TPublicOutput
                                      | 3 => Times Nat Nat
                                      | _ => Unit
                                      end.
Definition my_T_in := Sum Unit TInterrupt. (*We need Unit input to be able to differentiate trace, otherwise we only have interrupts in the trace*)
Definition my_T_out := Option (Sum TPublicOutput TTypeSyscall).
Definition my_T_in' := Times (Times Nat Nat) (times_Option_n 3 my_f_I).
Definition my_T_out' := times_Option_n 3 my_f_O.


(*Process*)

Definition alternate_generic (A B C: Ty) (x y : [B]) (z : [C]) := @map _ (Sum _ _) (Sum _ (Times Bool C)) B 
                        inl
                        (fun o => if o is inr (true,z) then x else y)
                        (@loop (Sum A (Times Bool C))
                        (@map (Sum A _) _ _ (Sum _ _) id (fun o => inr o)
                        ((@sta (Sum _ _) _ Bool
                           (fun i v => if i is inl _ then true else false)
                           (fun o v => v)
                           false
                           (@out (Times Bool _ ) C z)
                        )))).

Definition alternate_generic2 (A B C : Ty) (x y : [B]) (z : [C]) (pred : [A] -> bool) :=
  @map _ (Sum _ _) (Sum _ (Times Bool C)) B 
                        inl
                        (fun o => if o is inr (true,z) then x else y)
                        (@loop (Sum A (Times Bool C))
                        (@map (Sum A _) _ _ (Sum _ _) id (fun o => inr o)
                        ((@sta (Sum _ _) _ Bool
                           (fun i v => match i with | inl i' => v || pred i' | _ => false end)
                           (fun o v => v)
                           false
                           (@out (Times Bool _ ) C z)
                        )))).

Definition scheduled_process_pool
  (n : nat)
  (f_coopt : nat -> bool)
  (f_initial : nat -> bool)
  (f_I f_O : nat -> Ty)
  (f_proc : forall n, Proc (f_I n) (f_O n)) : Proc (Times (Times Nat Nat) ((times_Option_n n f_I))) (times_Option_n n f_O).
  elim: n.
  - simpl.
    eapply map. simpl.
      instantiate (1:= Times Bool (Option (f_I 0))). exact (fun n => ((0.+1 \in [:: fst (fst n); snd (fst n)],snd n))).
      exact id. 
    eapply swi. exact (f_initial 0.+1). 
    eapply maybe. 
    eapply map.
      eapply id. 
      exact (fun o => (f_coopt 0.+1,o)).
    exact (f_proc 0).

  - intros. simpl.
    eapply par.
    * eapply map.
      instantiate (1:= Times Bool (Option (f_I n.+1))). simpl.
      exact (fun x => ((n.+2) \in [:: fst (fst x); snd (fst x)], fst (snd x))).
        exact id. 
      eapply swi.
        exact (f_initial n.+2). 
      eapply maybe.
      eapply map.
        exact id.     
        exact (fun o => (f_coopt n.+2,o)).
      (*eapply maybe.*) (*not necessary anymore*)
      exact (f_proc n.+1).
    * eapply map. 3: apply H. simpl. 
      exact (map_pair id snd).
      exact id. 
Defined.

Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.

Definition only_loop
  (T_in' T_out' : Ty)   
  (f_route : [T_out'] -> [T_in'])
  (def : [T_out'])
  (p : Proc T_in' T_out')
  : Proc T_in' T_out' :=
  (@map T_in' (Sum T_in' T_out') (Sum T_in' T_out') T_out' inl (inr_or_def def)
                          (@loop (Sum T_in' T_out')
                             (@map (Sum T_in' T_out')
                                    T_in'
                                    _
                                    (Sum _ _)
                                (fun i  =>
                                   match i with
                                   | inl i' => i'
                                   | inr o  => f_route o (*i tilfælde hvor vi både ændrer switch og rerouter input, problem?*)
                                   end) inr
                                p))).

Definition low_p := @out Unit TPublicOutput GetRequest.
Definition handler := @alternate_generic TInterrupt THandlerOutput Unit2 Notify Nothing tt.
Definition high_p := @alternate_generic2 THandlerOutput TTypeSyscall Unit1 Syscall NOP tt (fun i => i == Notify).

(*
From:

private on ->(?timerinterrupt)
private on, scheduler on ->(!(handler_index,private_out))
handler on ->(!handler_out)
scheduler on ->(!public_index)
public on ->(?timerinterrupt)
public on, scheduler on ->(!(handler_index,public_out))
handler on ->(!handler_out)
scheduler on ->(!private_index)
...


To:

private on ->(?timerinterrupt)
private on ->(!private_out)
scheduler on ->(!handler_index)
handler on ->(!handler_out)
scheduler on ->(!public_index)
public on ->(?timerinterrupt)
public on ->(!public_out)
scheduler on ->(!handler_index)
handler on ->(!handler_out)
scheduler on ->(!private_index)
...
 *)
Definition good_schedulerp :  Proc (Sum TInterrupt THandlerOutput) (Times Nat Nat). (*handlerflag, processflag*) Check sta_NI. Check swi_NI. 
  eapply map. apply id. instantiate (1:= Times (Times Bool Bool) Unit).
  exact (fun o => match fst o with | (true,false) => (3,1) | (true,true) => (2,1) | (false,true) => (3,3) | (false,false) => (2,2) end ).
  eapply (@sta _ _ _). exact (fun ih bb => match ih with | inl TimerInterrupt => (true,~~ (snd bb))
                                                         | inr _ => (false,snd bb)
                                                         | _ => bb          
                                           end).
  exact (fun _ bb => bb).
  exact (false,false).
  eapply out. con.
Defined.

Definition sstream := Stream ([(Sum TInterrupt THandlerOutput)] + [(Times Nat Nat)]).

Definition my_sstreamF (s : sstream) := Cons (inl (inl TimerInterrupt)) (Cons (inr (2,1)) (Cons (inl (inr Nothing)) (Cons (inr (3,3))
                                                                                                                      (Cons (inl (inl TimerInterrupt)) (Cons (inr (3,1)) (Cons (inl (inr Nothing)) (Cons (inr (2,2)) s))))))).

CoFixpoint my_sstream := my_sstreamF my_sstream.

Lemma my_sstream_eq : my_sstream = my_sstreamF my_sstream.
Proof.
rewrite {1}/my_sstream.
rewrite {1}(coseq_match (cofix my_sstream : sstream := my_sstreamF my_sstream)).
simpl.
rewrite /my_sstreamF.
do ? f_equal.
Qed.

Lemma schedulerp_trace : trace my_sstream good_schedulerp.
Proof.
  pcofix CIH.
  rewrite my_sstream_eq /my_sstreamF /good_schedulerp.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;right.
Qed.


Definition unit_p : Proc Unit Unit := @out Unit Unit tt.

Definition my_procs_good : forall n, Proc (my_f_I n) (my_f_O n).
  case. apply handler.
  case. apply high_p.
  case. apply low_p.
  case. simpl. apply good_schedulerp.
  elim. apply unit_p.
  intros. apply unit_p.
Defined.



Definition my_f_coopt n := n == 4.
Definition my_f_initial n := n == 2.
Definition process_pool_good := @scheduled_process_pool 3 my_f_coopt my_f_initial my_f_I my_f_O my_procs_good.


Definition LoopType_n (n : nat) (f_I f_O : nat -> Ty) := Sum (times_Option_n n f_I) (times_Option_n n f_O).
Definition None_N (n : nat) (f_O : nat -> Ty) : [(times_Option_n n f_O)].
elim: n. simpl. exact None.
intros. simpl. eapply pair. exact None. exact H.
Defined.
Definition collapse_in_out (n : nat) (f_I f_O : nat -> Ty) (x : [LoopType_n n f_I f_O]) : [times_Option_n n f_O]  :=
  match x with
  | inl _ => None_N n f_O
  | inr x' => x'
  end.
Definition my_def := None_N 3 my_f_O.
Definition none4 : [ (times_Option_n 3 my_f_I) ]  := (None,(None,(None,None))).
Definition my_f_route_good (t : [my_T_out']) : [my_T_in'] :=
  match t with
  | (Some sch,_) => (sch,none4)
  | (_ ,(Some publ, _)) => ((0,0),none4)
  | (_ ,(None,(Some prv,_))) => ((0,0),none4)
  | (_ ,(None,(None,Some handl))) => ((1,4),(Some (inr handl),(None,(Some handl,None)))) (*(1,4) = turn off yourself, turn on scheduler*)
  | _ => ((0,0),none4)    
  end.

Definition my_f_in_sch_good (t : [my_T_in]) : [Times Nat Nat] := match t with | inl tt | inr DiskInterrupt => (0,0) | inr TimerInterrupt => (0,4) end.
Definition my_f_in_t (t : [my_T_in]) : [ (times_Option_n 3 my_f_I) ] := match t with
                                                                        | inl tt => (None,(Some tt,(None,None)))
                                                                        | inr TimerInterrupt => (Some (inl TimerInterrupt),(None,(None,None)))
                                                                        | inr DiskInterrupt => (None,(None,(None,Some DiskInterrupt))) end.
Definition my_f_in_good (t : [my_T_in]) : [my_T_in'] := (my_f_in_sch_good t, my_f_in_t t).
Definition my_f_out (t : [my_T_out']) := match t with
                                         | (_,(Some p,(None,None))) => Some (inl p)
                                         | (_,(None,(Some sys,None))) => Some (inr sys)
                                         | _ => None
                                         end.

Definition f_out_dis (v : [my_T_out]) := match v with | Some (inl _) | None => False | _  => True end.

Definition my_f_out_rel : myrel ([my_T_out]).
  refine (@MyRel _
            (fun l (v : [my_T_out]) => l = \bot /\ f_out_dis v )
            (fun l v1 v2 => v1 = v2 \/ (l = \bot /\ f_out_dis v1 /\ f_out_dis v2))
            _
            _
            _
            _).
  intros. con. intro. auto. intro. intros. de H.
  intro. intros. de H. de H0. left. subst. auto. subst. eauto.
  de H0. subst. eauto.
  intros. de H0.
  intros. ssa. subst. apply order_bot in H. subst. ssa.
  intros. ssa. subst. rewrite /order in H.  rewrite lex0 in H. by apply/eqP.
  ssa.
  con. case. intros. eauto.
  case. intros. subst. eauto.
  ssa.
Defined.

Definition my_only_loop_good' := @only_loop my_T_in' my_T_out' my_f_route_good my_def process_pool_good.

Definition my_only_loop_good : Proc my_T_in my_T_out .
  eapply map. apply my_f_in_good. apply my_f_out. apply my_only_loop_good'.
Defined.

  

Definition out0 x : [my_T_out'] := (Some x,(None,(None,None))).
Definition out1 x : [my_T_out'] := (None,(Some x,(None,None))).
Definition out2 x : [my_T_out'] := (None,(None,(Some x,None))).
Definition out3 x : [my_T_out'] := (None,(None,(None, Some x))).

(*Spec for good scheduler*)
(*Add diskinterrupt*)
Definition streamType' := Stream ([my_T_in'] + [my_T_out']).
Definition newtrace'F (s : streamType') := Cons (inl (my_f_in_good (inr TimerInterrupt))) (*jump to scheduler*)
                                             (Cons (inr ((Some (2,1)),(None,(Some NOP,None)))) (*private process does nothing, scheduler points to handler*)
                                             (Cons (inr (out3 Nothing)) (*handler finishes, returns control to scheduler*)
                                             (Cons (inr (out0 (3,3))) (*scheduler points to public*)
                                             (Cons (inr (out1 GetRequest)) (*public output*)
                                             (Cons (inl (my_f_in_good (inr DiskInterrupt)))(*disk interrupt, should NOT jump to handler*)
                                             (Cons (inl (my_f_in_good (inr TimerInterrupt))) (*jump to scheduler*)
                                             (Cons (inr (Some (3,1),(Some GetRequest,(None,None)))) (*public process finishes, scheduler points to handler*)
                                             (Cons (inr (out3 Notify)) (*handler signal informs diskinterrupt was received*)
                                             (Cons (inr (out0 (2,2))) (*scheduler points to private*)
                                             (Cons (inr (None,(None,(Some Syscall,None)))) s)))))))))) (*private output received notification from handler, outputs new syscall*).

CoFixpoint newtrace' := newtrace'F newtrace'.

Lemma newtrace'_eq : newtrace' = newtrace'F newtrace'.
Proof.
rewrite {1}/newtrace'.
rewrite {1}(coseq_match (cofix newtrace' : streamType' := newtrace'F newtrace')).
simpl.
rewrite /newtrace'F.
do ? f_equal.
Qed.



Definition streamType := Stream ([my_T_in] + [my_T_out]).

Definition newtraceF (s : streamType) := Cons (inl (inr TimerInterrupt))
                                            (Cons (inr (Some (inr NOP)))
                                             (Cons (inr None)
                                             (Cons (inr None)
                                             (Cons (inr (Some (inl GetRequest)))
                                             (Cons (inl (inr DiskInterrupt))
                                             (Cons (inl (inr TimerInterrupt))
                                             (Cons (inr (Some (inl GetRequest)))
                                             (Cons (inr None)
                                             (Cons (inr None)
                                             (Cons (inr (Some (inr Syscall))) s)))))))))).

CoFixpoint newtrace := newtraceF newtrace.

Lemma newtrace_eq : newtrace = newtraceF newtrace.
Proof.
rewrite {1}/newtrace.
rewrite {1}(coseq_match (cofix newtrace : streamType := newtraceF newtrace)).
simpl.
rewrite /newtraceF.
do ? f_equal.
Qed.


Ltac rewr ::=  (try rewrite newtrace'_eq); (try rewrite newtrace_eq); rewrite /low_p /handler /high_p /only_loop /my_only_loop_good' /my_only_loop_good /process_pool_good /good_schedulerp /my_f_coopt /scheduled_process_pool /high_p /alternate_generic /alternate_generic2 /low_p.

(*spec for good scheduler*)
Lemma newtrace'_trace : trace newtrace' my_only_loop_good'.
Proof.
  pcofix CIH. 
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  instantiate (1:= 0). instantiate (1:= 0). instantiate (1:= 0). simpl.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;right.
  swi_instans. simpl. eauto.
Qed.


(*spec for good scheduler (what the world sees)*)
Lemma newtrace_trace : trace newtrace my_only_loop_good.
Proof.
  pcofix CIH.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.  
  bundle;left.
  bundle.
  instantiate (2:= None). simpl.
  instantiate (1:= None). simpl. done.
  instantiate (3:=0). simpl. reduce_once. econ.
  reduce_tac.
  instantiate (2:= 0). simpl.
  reduce_once.
  instantiate (2:= 0). simpl.
  reduce_once.
  simpl. reduce_once. econ.
  reduce_tac.
  reduce_tac.
  reduce_tac.
  reduce_tac.
  left.
  
  bundle;left.
  bundle;left.  
  bundle;right.
  swi_instans.
  eauto.
Qed.





(*Now the bad process*)


(*
private on ->(?tI)
private on, scheduler on ->(!public)
public on ->(?dI)
public on, handler on -> !(public,notification)
public on ->(?tI)
scheduler on, public on ->(!handler)
handler on ->(!notification)
scheduler on ->(!private)
...
 *)
Definition good_schedulerp :  Proc (Sum TInterrupt THandlerOutput) (Times Nat Nat). (*handlerflag, processflag*)
  eapply map. apply id. instantiate (1:= Times (Times Bool Bool) Unit).
  exact (fun o => match fst o with | (true,false) => (3,1) | (true,true) => (2,1) | (false,true) => (3,3) | (false,false) => (2,2) end ).
  eapply (@sta _ _ _). exact (fun ih bb => match ih with | inl TimerInterrupt => (true,~~ (snd bb))
                                                         | inr _ => (false,snd bb)
                                                         | _ => bb          
                                           end).
  exact (fun _ bb => bb).
  exact (false,false).
  eapply out. con.
Defined.
