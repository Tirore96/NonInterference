Set Implicit Arguments.

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
(*ltacs*)

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


(* Types *)

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



Inductive Ty : Set := Nat | Times : Ty -> Ty -> Ty | Bool | Option : Ty -> Ty | TInput | TOutput.

Derive NoConfusion for Ty.
Derive EqDec for Ty.

Definition Ty_indDef := [indDef for Ty_rect].
Canonical Ty_indType := IndType Ty Ty_indDef.
Definition Ty_hasDecEq := [derive hasDecEq for Ty].
HB.instance Definition _ := Ty_hasDecEq.

Fixpoint interp (t : Ty) : Set :=
  match t with
  | Nat => nat
  | Times t0 t1 => (interp t0) * (interp t1)%type
  | Bool => bool
  | Option t' => option (interp t')
  | TInput => Input
  | TOutput => Output              
  end.
Notation "[ i ]" := (interp i).

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



(** Core combinators *)
(*Parameter map   : forall {I I' O O'}, (I -> I') -> (O -> O') -> Proc I' O -> Proc I O'.
Parameter sta   : forall {I O V}, (I -> V -> V) -> (O -> V -> V) -> V -> Proc (V*I) O -> Proc I (V*O).
Parameter swi   : forall {I O},  bool -> Proc I (bool * O)%type -> Proc (bool * I) (option O).
Parameter par   : forall {I O1 O2}, Proc I O1 -> Proc I O2 -> Proc I (O1 * O2).
Parameter loop  : forall {I}, Proc I I -> Proc I I.
Parameter maybe : forall {I O}, Proc I O -> Proc (option I) O.*)

Definition xor (b1 b2 : bool) := (Datatypes.negb (b1 == b2)).


Check out.

Inductive reduceI : forall (I O : Ty), Proc I O -> interp I -> Proc I O -> Prop :=
| reduce_outI I O i (o : [O]) : reduceI (@out I _ o) i (@out I _ o)
| reduce_mapI (I I' O O' : Ty) p p' i i' (f : [I] -> [I']) (g : [O] -> [O']) : f i = i' -> reduceI p i' p' -> reduceI (map f g p) i (map f g p')
| reduce_staI (V I O : Ty) v v' (p : Proc (Times V I) O) p' i (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) : f i v = v' -> reduceI p (v', i) p' -> reduceI (sta f g v p) i (sta f g v' p')
| reduce_swiI (I O : Ty) b b' b'' (p : Proc I (Times Bool O)) p' (i : [I]) : b'' = xor b b' -> reduceI p i p' -> reduceI (swi b p) (b', i) (swi b'' p')
| reduce_maybeI (I O : Ty) (p : Proc I O) : reduceI (maybe p) None (maybe p)
| reduce_maybeI2 (I O : Ty) (p p' : Proc I O) (i : [I]) : reduceI p i p' -> reduceI (maybe p) (Some i) (maybe p')
| reduce_parI (I O1 O2 : Ty) (p1 p1' : Proc I O1) (p2 p2' : Proc I O2) (i : [I]) : reduceI p1 i p1' -> reduceI p2 i p2' -> reduceI (par p1 p2) i (par p1' p2')
| reduce_loopI (I :Ty) (p p' : Proc I I) (i : [I]) : reduceI p i p' -> reduceI (loop p) i (loop p').
Hint Constructors reduceI.

Inductive reduceO : forall (I O : Ty), Proc I O -> [O] -> Proc I O -> Prop :=
| reduce_outO (I O : Ty) (o : [O]) : reduceO (@out I _ o) o (@out I _ o)
| reduce_mapO (I I' O O' : Ty) p p' o o' (f : [I] -> [I']) (g : [O] -> [O']) : g o = o' -> reduceO p o p' -> reduceO (map f g p) o' (map f g p')
| reduce_staO (V I O : Ty) v v' p p' o (f : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V]) : g o v = v' -> reduceO p o p' -> reduceO (sta f g v p) (v', o) (sta f g v' p')
| reduce_swiO (I O : Ty) (p : Proc I (Times Bool O)): reduceO (swi false p) None (swi false p)
| reduce_swiO2 (I O : Ty) b b' (p : Proc I (Times Bool O)) p' (o : [O]) : b' = xor true b -> reduceO p (b, o) p' -> reduceO (swi true p) (Some o) (swi b' p')
| reduce_maybeO (I O : Ty) (p p' : Proc I O) (o : [O]) : reduceO p o p' -> reduceO (maybe p) o (maybe p')
| reduce_parO (I O1 O2 : Ty) (p1 p1' : Proc I O1) (p2 p2' : Proc I O2) (o : [O1]) (o' : [O2]) : reduceO p1 o p1' -> reduceO p2 o' p2' -> reduceO (par p1 p2) (o, o') (par p1' p2')
| reduce_loopO (O :Ty) (p p' p'' : Proc O O) (o : [O]) : reduceO p o p' -> reduceI p' o p'' -> reduceO (loop p) o (loop p'').
Hint Constructors reduceO.




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

(* not (a -> b)  = *)  
Definition trace (I O : Ty) eff p := paco2 (@TraceF I O) bot2 eff p.


Variant Clause1 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | Clause1F : forall p i s, (dis IRel l i -> R s p) -> Clause1 l IRel ORel R (Cons (inl i) s) p.


Variant Clause2 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | Clause2F : forall p s, (forall i, dis IRel l i -> exists p', reduceI p i p' /\ R s p') -> Clause2 l IRel ORel R s p.


Variant Clause3 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | Clause3F : forall p i s, (forall i', rel IRel l i i' -> exists p', reduceI p i' p' /\ R s p')
                         -> Clause3 l IRel ORel R (Cons (inl i) s) p.

Variant Clause4 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | Clause4F : forall p p' o o' s,  rel ORel l o o' -> reduceO p o' p' -> R s p' -> Clause4 l IRel ORel R (Cons (inr o) s) p.


(*Variant Simulation'F {I O : Set} (l : level) (IRel : myrel I) (ORel : myrel O) (R : Stream (I + O) -> Proc I O -> Prop) : Stream (I + O) -> Proc I O  -> Prop :=
  | SI13 : forall p i s, (forall i', rel IRel l i i' -> exists p', reduceI p i' p' /\ R s p')
                         -> Simulation'F l IRel ORel R (Cons (inl i) s) p
  | SI4 : forall p p' o o' s,  rel ORel l o o' -> reduceO p o' p' -> R s p' -> Simulation'F l IRel ORel R (Cons (inr o) s) p.
Hint Constructors Simulation'F.*)

Variant SimulationF {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | SI s p : Clause1 l IRel ORel R s p ->
             Clause2 l IRel ORel R s p ->
             Clause3 l IRel ORel R s p ->
             Clause4 l IRel ORel R s p ->
             SimulationF l IRel ORel R s p.


(*(*TODO: Check definition with Willard*)
Variant SimulationF {I O : Set} {l : level} {IRel : myrel I} {ORel : myrel O} (R : Stream (I + O) -> Proc I O -> Prop) : Stream (I + O) -> Proc I O  -> Prop :=
  | NI13 : forall p p' i s,  (dis IRel l i -> R s p') \/ (forall i', rel IRel l i i' -> exists p', reduceI p i' p' /\ R s p')  -> SimulationF R (Cons (inl i) s) p
  | NI2 : forall p s,  (forall i, dis IRel l i -> exists p', reduceI p i p' /\ R s p')  -> SimulationF R s p
  | NI4 : forall p p' o o' s, rel ORel l o o' -> reduceO p o' p' -> SimulationF R (Cons (inr o) s) p.
Hint Constructors SimulationF.*)


Lemma monotone_SimulationF {I O : Ty}  l IRel ORel :  monotone2 (@SimulationF I O l IRel ORel).
Proof.
rewrite /monotone2. ssa.
inv IN.
eauto. Admitted.

(*eapply NI2. 
intros. move: (H _ H0). case.
eauto. ssa. eauto.
eapply NI3.  intros.
move: (H _ H0). case. eauto.
eauto. ssa. eauto.
subst. eauto.
Qed.*)
Hint Resolve monotone_SimulationF : paco.

Definition simulation {I O : Ty} l IRel ORel s p := paco2 (@SimulationF I O l IRel ORel) bot2 s p.

Inductive NotSim {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) : Stream ([I] + [O]) -> Proc I O -> Prop :=
| NS1 i s p : dis IRel l i -> NotSim l IRel ORel s p -> NotSim l IRel ORel (Cons (inl i) s) p
| NS2 i s p : dis IRel l i -> (forall p', reduceI p i p' -> NotSim l IRel ORel s p') -> NotSim l IRel ORel s p
| NS3 i s p : (forall p', (exists i', rel IRel l i i' /\ reduceI p i' p') ->  NotSim l IRel ORel s p') -> NotSim l IRel ORel (Cons (inl i) s) p
| NS4 o s p : (forall p' o', rel ORel l o o' -> reduceO p o' p' -> NotSim l IRel ORel s p') -> NotSim l IRel ORel (Cons (inr o) s) p.

(*Lemma NotSim_ind
     : forall (I O : Set) (l : level) (IRel : myrel I) (ORel : myrel O) (P : Stream (I + O) -> Proc I O -> Prop),
       (forall (i : I) (s : Stream (I + O)) (p : Proc I O), dis IRel l i -> NotSim l IRel ORel s p -> P s p -> P (Cons (inl i) s) p) ->
       (forall (i : I) (s : Stream (I + O)) (p : Proc I O),
        dis IRel l i -> (forall p' : Proc I O, reduceI p i p' -> NotSim l IRel ORel s p') -> (forall p' : Proc I O, reduceI p i p' -> P s p') -> P s p) ->
       (forall (i : I) (s : Stream (I + O)) (p : Proc I O), (forall p' : Proc I O, exists i' : I, rel IRel l i i' /\ reduceI p i' p' -> P s p' -> NotSim l IRel ORel s p') -> P (Cons (inl i) s) p) ->
       (forall (o : O) (s : Stream (I + O)) (p : Proc I O),
        (forall (p' : Proc I O) (o' : O), rel ORel l o o' -> reduceO p o p' -> NotSim l IRel ORel s p') ->
        (forall (p' : Proc I O) (o' : O), rel ORel l o o' -> reduceO p o p' -> P s p') -> P (Cons (inr o) s) p) ->
       forall (s : Stream (I + O)) (p : Proc I O), NotSim l IRel ORel s p -> P s p.
Proof.
  move=> I O l IRel ORel P H1 H2 H3 H4.
  fix IH 3.
  move=> s p [].
  - intros. apply H1. done. done. apply IH. done.
  - intros. eapply H2. eauto. done. intros. apply IH. eauto. 
  - intros. eapply H3. intros.
    case: (e p'). ssa. exists x. case.
    done. intros. apply IH. eauto. *)

    
Ltac pc := pclearbot.
Definition streampred (I O : Set) l (IRel : myrel I) (ORel : myrel O) (s : Stream (I + O))  := ForAll (fun x => match x with | Cons (inl x') _ => dis IRel l x' | Cons (inr x') _ => dis ORel l x' end) s.

Lemma rel_eq : forall (I : Set) (IRel : myrel I) (x : I) l, rel IRel l x x.
Proof.
  intros. de IRel. ssa.
  move: (equiv0 l). case. move=> Hr _ _. apply Hr.
Qed.
Hint Resolve rel_eq.

Lemma toNotSim : forall {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) s (p : Proc I O), NotSim l IRel ORel s p -> ~simulation l IRel ORel s p.
Proof.
  move=> I O l IRel ORel s p H Hsim.
  elim: H Hsim;intros.
  - punfold Hsim. inv Hsim.
    clear H3 H4 H5. inv H2. pc. 
    by move: (H6 H).
  - punfold Hsim. inv Hsim.
    clear H2 H4 H5. inv H3.
    case: (H2 _ H)=>p1 [] Hred [] Hsim'//;eauto.
  - punfold Hsim. inv Hsim.
    clear H1 H2 H4. inv H3.
    case: (H5 _ (rel_eq IRel i l))=>p1 [] Hred []// Hsim'.
    eapply H0. 2:eauto. exists i. eauto.
  - punfold Hsim. inv Hsim.
    clear H1 H2 H3. inv H4. pc.
    move: (H0 _ _ H3 H5). eauto.
Qed.
  
Section AdmittedTheorems.

Definition NI {I O :Ty} IRel ORel (p : Proc I O) := forall l s p, trace s p -> @simulation I O l IRel ORel s p.

Definition f_NI {I O :Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O]) := forall (l : level) (i i' : [I]) (o o' : [O]), rel IRel l i i' -> rel ORel l (f i) (f i').
Definition f_PU {I O : Ty} (IRel : myrel [I]) (ORel : myrel [O]) (f : [I] -> [O]) := forall l (i : [I]), dis IRel l i -> dis ORel l (f i).

Lemma map_NI : forall (I I' O O' : Ty) (p : Proc I' O) (f : [I] -> [I']) (g : [O] -> [O']) (IRel : myrel [I]) (IRel' : myrel [I']) (ORel : myrel [O]) (ORel' : myrel [O']), NI IRel' ORel p -> f_NI IRel IRel' f -> f_PU IRel IRel' f -> f_NI ORel ORel' g -> NI IRel ORel' (map f g p).
Admitted.


Definition fv_NI {I O V: Ty} (f : [I] -> [V] -> [O]) (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O]) := forall l (i i' : [I]), rel IRel l i i' -> forall (v v' : [V]), rel VRel l v v' -> rel ORel l (f i v) (f i' v').

Definition equivalence_preserving {I V: Ty} (f : [I] -> [V] -> [V]) (IRel : myrel [I]) (VRel : myrel [V]) := forall l i, dis IRel l i -> forall v, rel VRel l (f i v) v.

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



 Theorem sta_NI : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O]), NI (eqpair_LR VRel IRel) ORel p -> fv_NI g ORel VRel VRel -> fv_NI f IRel VRel VRel -> equivalence_preserving f IRel VRel -> NI IRel (eqpair VRel ORel) (sta f g v p).
 Admitted.



Definition aware (V : Set) (VRel : myrel V) (l : level) (v : V) := (forall v', rel VRel l v v' -> v = v') /\ ~ dis VRel l v.

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

Definition oblivious {I O : Ty} (ORel : myrel [O]) (l : level) p := paco1 (@ObliviousF I O ORel l) bot1 p.

Definition boolRel : myrel ([Bool]).
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

Definition order_respecting (ls : seq level) :=  forall l l', order l l' -> l \in ls -> l' \in ls.

Definition eqmaybe {V : Ty} (VRel : myrel [V]) (ls : seq level) : myrel ([Option V]).
    refine (@MyRel _
            (fun l v => if v is Some v' then dis VRel l v' else forall l', l' <= l -> l' \notin ls)
            (fun l b1 b2 => b1 = b2)
            _
            _
            _
            _).
intros. auto.
ssa. de a.
de VRel. eauto.
apply/negP. intro.
have: l' <= l1.
apply: le_trans. eauto. done.
move/(H0 _). by rewrite H2.

intros. de a0. de a1. inv H0. subst. done.
subst. done.
Defined.


Theorem swi_NI : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) ls p b, NI IRel (eqpair_LR boolRel ORel) p -> (forall l, l \in ls -> aware boolRel l true \/ oblivious (eqpair_LR boolRel ORel) l p) -> NI (eqpair_LR boolRel IRel) (eqmaybe ORel ls) (swi b p).
Admitted.


Theorem maybe_NI : forall (I O :Ty) (IRel : myrel [I]) (ORel : myrel [O]) p, NI IRel ORel p -> NI (eqmaybe IRel nil) ORel (maybe p).
Admitted.

Theorem loop_NI : forall (I : Ty) (IRel : myrel [I]) p, NI IRel IRel p -> NI IRel IRel (loop p).
Admitted.

Theorem par_NI : forall (I O1 O2 : Ty) (IRel : myrel [I]) (ORel1 : myrel [O1]) (ORel2 : myrel [O2]) p1 p2, NI IRel ORel1 p1 -> NI IRel ORel2 p2 -> NI IRel (eqpair ORel1 ORel2) (par p1 p2).
Admitted.

End AdmittedTheorems.


Definition mapO {I O O' : Ty} (f : [O] -> [O']) : Proc I O  -> Proc I O' :=
  map (@id [I]) f.


(*** Message transformation *)
Definition mapI {I I' O : Ty} (f : [I] -> [I']) : Proc I' O -> Proc I O := map f (@id [O]).
Definition mapO_version {I O O' : Ty} (f : [O] -> [O']) : Proc I O  -> Proc I O' := map (@id [I]) f.

Definition staI {I O V : Ty} (f : [I] -> [V] -> [V]) (v:[V]) (p:Proc (Times V I) O) : Proc I (Times V O) :=
  sta f (fun o v => v) v p.
Definition staO {I O V : Ty} (f : [O] -> [V] -> [V]) (v:[V]) (p:Proc (Times V I) O) : Proc I (Times V O) :=
  sta (fun i v => v) f v p.



(*** Process switching *)

Definition swiI {I O : Ty} (b : [Bool]) (p : Proc I O) : Proc (Times Bool I) (Option O) :=
  swi b (@mapO _ _ (Times Bool _) (fun x => (false,x)) p).
Definition swiO {I O : Ty} (b : bool) (p : Proc I (Times Bool O)) : Proc I (Option O) :=
  @mapI _ (Times Bool _) _ (fun x => (false,x)) (swi b p).

Definition par_swiI {I1 I2 O1 O2} (b:bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2)
  : Proc (Times Bool (Times I1 I2)) (Times (Option O1) (Option O2)) :=
    par
      (swi b (@map (Times _ _) _ _ (Times Bool _) fst (fun x => (false,x)) p1))
      (swi (negb b) (@map (Times _ _) _ _ (Times Bool _) snd (fun x => (false,x)) p2)).

(** Inputs / Outputs*)




(*Simple example*)
Check out.
Definition p1_simple := @out TInput TOutput Step.
Definition p2 := @out TInput TOutput Idle.
Definition processes_simple (*: Proc (bool * (I1 * I2)) (O1 + O2) :=*) :=
  par_swiI false p1_simple p2.

Definition leaking_scheduler := @map _ (Times Bool (Times TInput TInput)) _ _ (fun (i : [Times TInput TInput]) => (fst i == DiskRead,i)) id processes_simple.


Definition scheduler_stream := Stream ([Times TInput TInput] + (([Times (Option TOutput) (Option TOutput)]))).
Definition newtraceF_simple (newtrace : scheduler_stream) := Cons (inl (DiskRead,Skip))
                                                               (Cons (inr (Some Step,None))
                                                                  (Cons (inl (DiskRead,Skip)) newtrace)).

CoFixpoint newtrace_simple := newtraceF_simple newtrace_simple.

Lemma newtrace_simple_eq : newtrace_simple = newtraceF_simple newtrace_simple.
Proof.
rewrite {1}/newtrace_simple.
rewrite {1}(coseq_match (cofix newtrace : scheduler_stream := newtraceF_simple newtrace)).
simpl.
rewrite /newtraceF_simple.
do ? f_equal.
Qed.

Lemma newtrace_simple_eq2 s : newtraceF_simple s =  Cons (inl (DiskRead,Skip))
                                                               (Cons (inr (Some Step,None))
                                                                  (Cons (inl (DiskRead,Skip)) s)).
Proof. done.
Qed.

Section EQs.
Let eqs := (newtrace_simple_eq, newtrace_simple_eq2).

Ltac peel := pfold;econ;first econs;simpl;left.
Ltac finish := by pfold;econ;first econs;simpl;right.
Check trace.


Ltac rewr :=
  (try rewrite newtrace_simple_eq); rewrite /newtraceF_simple /processes_simple /par_swiI /leaking_scheduler /p1_simple /p2.

Ltac swi_instans :=
   repeat
    match goal with
    | |- context [ swi (?x < ?x) _] => is_evar x; unify x 0
    end; rewrite ?eqxx /= /xor /=.


Ltac reduce_tac :=
  rewr;
   repeat
    match goal with
    | |- reduceI (@out _ _ _) _ _ => apply: reduce_outI
    | |- reduceI (@map _ _ _ _ _ _ _) _ _ => apply: reduce_mapI
    | |- reduceI (@sta _ _ _ _ _ _ _) _ _ => apply: reduce_staI
    | |- reduceI (@swi _ _ _ _) _ _ => apply: reduce_swiI
    | |- reduceI (par _ _) _ _ => apply: reduce_parI
    | |- reduceI (@loop _ _) _ _ => apply: reduce_loopI                                                  
    | |- reduceI (@maybe _ _ _ _ _ _ _) None _ => apply: reduce_maybeI
    | |- reduceI (@maybe _ _ _ _ _ _ _) (Some _) _ => apply: reduce_maybeI2

    | |- reduceO (@out _ _ _) _ _ => apply: reduce_outO
    | |- reduceO (@map _ _ _ _ _ _ _) _ _ => apply: reduce_mapO
    | |- reduceO (@sta _ _ _ _ _ _ _) _ _ => apply: reduce_staO
    | |- reduceO (swi _ _) None _ => apply: reduce_swiO
    | |- reduceO (swi _ _) (Some _) _ => apply: reduce_swiO2
    | |- reduceO (par _ _) _ _ => apply: reduce_parO
    | |- reduceO (@loop _ _) _ _ => apply: reduce_loopO
    | |- reduceO (@maybe _ _ _ _ _ _ _) _ _ => apply: reduce_maybeO
    end;(try swi_instans);eauto; rewrite ?eqxx /= /xor /=.

Ltac appTrace := apply: traceI || apply: traceO.


Ltac bundle :=
  pfold;
  appTrace;
  first (do ? reduce_tac).

Lemma simple_trace : trace newtrace_simple leaking_scheduler.
Proof.
  pcofix CIH.
  rewr.
  bundle. left.
  bundle. left.
  bundle. right.
  swi_instans. eauto.
Qed.  
  
Definition Input_prod : myrel ([Times TInput TInput]).
  apply: eqpair_LR. apply InputRel. apply InputRel.
Defined.
Check OutputRel.
Definition Output_option : myrel ([Option TOutput]) := eqmaybe OutputRel [::\top].

Definition Output_option_prod : myrel ([Times (Option TOutput) (Option TOutput)]).
  apply eqpair. apply Output_option. apply Output_option.
  Defined.

(*kort trace kunne være om der er diskread først eller ikke*)


Global Instance input_dec : EqDec Input.
Proof. intro. intro. destruct (eqVneq x y). left. done. right. intro. subst.
       apply/negP. apply i. rewrite eqxx. done.
Qed.

Global Instance output_dec : EqDec Output.
Proof. intro. intro. destruct (eqVneq x y). left. done. right. intro. subst.
       apply/negP. apply i. rewrite eqxx. done.
Qed.


Ltac dd H := dependent destruction H.

Ltac match_dd := 
   repeat
    match goal with
    | H : reduceI _ _ _ |- _ => dd H
    | H : reduceO _ _ _ |- _ => dd H
    end.

(*Uniqueness of Identity pro*)
Set Equations With UIP.
Example counterexample : NotSim \bot Input_prod Output_option_prod newtrace_simple leaking_scheduler.
Proof. Check NS2. 
  rewrite newtrace_simple_eq /newtraceF_simple.
  apply: NS2. instantiate (1:= (DiskRead,Skip)).
  rewrite /= eqxx. auto.

  intros. match_dd.

  apply: NS3. ssa. de x. subst.
  match_dd.
  
  apply: NS4. ssa. de o'. subst.
  match_dd.
Qed.  


Check NI.
Example example_not_NI :  ~ NI Input_prod Output_option_prod leaking_scheduler.
Proof.
  rewrite /NI. ssa. intro.
  Search _ NotSim.
  apply/toNotSim. apply/counterexample.
  apply/H. apply simple_trace.
Qed.  






Example counterexample : ~ simulation \bot Input_prod Output_option_prod newtrace_simple leaking_scheduler.
Proof.
intro.
rewrite /simulation in H.
punfold H.
inv H;pc.
- rewrite  newtrace_simple_eq in H0. inv H0.
  ssa. rewrite eqxx in H1.
  clear H1. punfold H2.
  inv H2.
 * admit.

  
Lemma not_simulation_simple : ~ 
  
(*Vi kan simplificere den høje process til kun at reagere på DiskRead i første omgang
  Vi kan tage mere specifik interrupt modellering i anden omgang*)
(*state: 1 = active, 2 = inactive*)
Definition p1 :=
  map id snd
  (sta (fun (i : Input) (v : nat) => match i,v with | Skip, _ => v | DiskRead, _ => 1 end)
    (fun (o : Output) (v : nat) => if o == Step then 2 else v )
    2
    (map (fun (vi : nat * Input) => ((fst vi == 1) && (snd vi == DiskRead),snd vi)) (fun o => if o is Some Step then Step else Idle)
       (swi false (out (true,Step))))).


Definition testtype := (Input + Output)%type.
Definition myinp (i : Input) : testtype := inl i.
Definition myout (o : Output) : testtype := inr (o).

Definition skipI := myinp Skip.
CoFixpoint skiptrace := Cons skipI skiptrace.

Definition idleO := myout Idle.
CoFixpoint idletrace := Cons idleO idletrace.

Definition diskreadI := myinp DiskRead.
Definition stepO := myout Step.


(*idle until diskread which produces a single step*)
Definition newtraceF (newtrace : Stream testtype) := Cons skipI (Cons idleO (Cons idleO (Cons diskreadI (Cons stepO (Cons skipI newtrace))))).

CoFixpoint newtrace := newtraceF newtrace.

Lemma newtrace_eq : newtrace = newtraceF newtrace.
Proof.
rewrite {1}/newtrace.
rewrite {1}(coseq_match (cofix newtrace : Stream testtype := newtraceF newtrace)).
simpl.
rewrite /newtraceF.
do ? f_equal.
Qed.

Notation "p0 || p1" := (par p0 p1).
Notation "! ( p )" := (out p)(at level 0, format "! ( p )").
Notation on p := (swi true p).
Notation off p := (swi false p).
Notation "f >> p >> g" := (map f g p)(at level 0).


Example myexample : trace newtrace p1.
Proof.
pcofix CIH.  
rewrite newtrace_eq /p1.
pfold;econ;first econs;left. simpl.
pfold;econ;first econs;left.
pfold;econ;first econs;left. 
pfold;econ;first econs;left.
pfold;econ;first econs;left.
pfold;econ;first econs;right.
rewrite //=.
Qed.

Definition newtraceF2 (newtrace : Stream testtype) := Cons idleO newtrace.
CoFixpoint newtrace2 := newtraceF2 newtrace2.
Lemma newtrace_eq2 : newtrace2 = newtraceF2 newtrace2.
Proof.
rewrite {1}/newtrace2.
rewrite {1}(coseq_match (cofix newtrace : Stream testtype := newtraceF2 newtrace)).
simpl.
rewrite /newtraceF2.
do ? f_equal.
Qed.

Example myexample2 : trace newtrace2 p2.
Proof.
pcofix CIH.  
rewrite newtrace_eq2 /p2.
by pfold;econ;first econs;right. 
Qed.





(*now do example of a trace that is not a simulation*)
Definition stream3 := Stream ((Input * Input) + ((option Output) * (option Output)))%type.
Definition newtraceF3 (newtrace : stream3) := Cons (inr (None,Some Idle))
                                                (Cons (inr (None,Some Idle))
                                                   (Cons (inr (None,Some Idle))
                                                      (Cons (inl (DiskRead, DiskRead))
                                                         (Cons (inr (Some Step,None))
                                                            (Cons (inr (Some Idle,None))
                                                                  (Cons (inl (Skip,DiskRead))
                                                              newtrace)))))).
CoFixpoint newtrace3 := newtraceF3 newtrace3.

Lemma newtrace_eq3 : newtrace3 = newtraceF3 newtrace3.
Proof.
rewrite {1}/newtrace3.
rewrite {1}(coseq_match (cofix newtrace := newtraceF3 newtrace)).
simpl.
rewrite /newtraceF3.
do ? f_equal.
Qed.


Example myexample3 : trace newtrace3 leaking_scheduler.
Proof.
pcofix CIH.  
rewrite newtrace_eq3.  
pfold;econ;first econs;left.
pfold;econ;first econs;left.
pfold;econ;first econs;left;simpl.
pfold;econ;first econs;left;simpl.
pfold;econ;first econs;left;simpl.
pfold;econ;first econs;left;simpl.
pfold;econ;first econs;right;simpl.
eauto.
Qed.


intro.
punfold H. rewrite newtrace_eq3 /newtraceF3 in H.
inv H;subst;pclearbot.
move: (H0 (DiskRead,DiskRead)).
have: dis Input_prod \bot (DiskRead, DiskRead).
simpl. eauto.
move=>HH. move/(_ HH).
case=>x.
ssa. pclearbot.
punfold H2. inv H2;subst.

have: reduceI leaking_scheduler (DiskRead, DiskRead) x.
 msimpl.
rewrite /dis.
simpl.

  
  leaking_scheduuler. (* Mitigator definition(s). Prevents interference as scheduling is round robin. *)
Definition naive_scheduler {I O} (p : Proc (bool * I) O) : Proc I O :=
  map (fun i => (true,i)) id p.


Definition naive_mitigator (*: Proc (I1 * I2) (O1 + O2) :=*) :=
  naive_scheduler processes.

Definition scheduler {I O : Set} n (p : Proc (bool * I) O) : Proc I O :=
  map id snd
    (sta (fun i v => ((fst v) + 1, ((fst v) %% n) == 0)) (fun o v => v) (0,false)
       (map (fun (nbi : ((nat * bool) * I)) => (snd (fst nbi) , snd nbi)) id
          p)).

Definition mitigator :=
  scheduler 10 processes.

Check mitigator.
