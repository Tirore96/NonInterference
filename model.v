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

(*Example 3*)
Inductive Interrupt := DiskInterrupt | TimerInterrupt.
Inductive HandlerOutput := Nothing | Notify.
Inductive TypeSyscall := Syscall.(* InternalStep | Syscall | Notify (*| Default*) . (* | SPublic. (*SPublic corresponds to None, and InternalStep/Syscall is Some _
                                                             Used to distinguish H/L and easier than sprinkling option types into existing counterexample
                                                            *)*) *)
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



(*Inductive TypeNotify := SysStep | Notify. (*| NPublic. (*NPublic corresponds to None*)*)

Definition TypeNotify_indDef := [indDef for TypeNotify_rect].
Canonical TypeNotify_indType := IndType TypeNotify TypeNotify_indDef.
Definition TypeNotify_hasDecEq := [derive hasDecEq for TypeNotify].
HB.instance Definition _ := TypeNotify_hasDecEq.*)




Inductive Ty : Set := Nat | Times : Ty -> Ty -> Ty | Bool | Option : Ty -> Ty | Sum : Ty -> Ty -> Ty | TInput | TOutput | TTypeSyscall | Unit | TInterrupt | THandlerOutput |  TPublicOutput. (* | TTypeNotify.*)

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
              (*  | TTypeNotify => TypeNotify   *)
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
Hint Constructors reduceI : core.

Create HintDb omitdb.
Hint Resolve reduce_mapI reduce_staI reduce_swiI reduce_maybeI reduce_maybeI2 reduce_parI reduce_loopI : omitdb.

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

Hint Resolve reduce_mapO reduce_staO reduce_swiO reduce_swiO2 reduce_maybeO reduce_parO reduce_loopO : omitdb.


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


Definition Clause1 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  forall i s', s = (Cons (inl i) s') -> dis IRel l i -> R s' p.


(*Variant Clause1 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | Clause1F : forall p i s s', s = (Cons (inl i) s') -> (dis IRel l i -> R s' p) -> Clause1 l IRel ORel R s p.*)

Definition Clause2 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  (forall i, dis IRel l i -> exists p', reduceI p i p' /\ R s p').


(*Variant Clause2 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | Clause2F : forall p s, (forall i, dis IRel l i -> exists p', reduceI p i p' /\ R s p') -> Clause2 l IRel ORel R s p.
 *)

Definition Clause3 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  forall i s', s = (Cons (inl i) s') -> (forall i', rel IRel l i' i -> exists p', reduceI p i' p' /\ R s' p').


(*Variant Clause3 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | Clause3F : forall p i s s', s = (Cons (inl i) s') -> (forall i', rel IRel l i i' -> exists p', reduceI p i' p' /\ R s' p')
                         -> Clause3 l IRel ORel R s p.
 *)

Definition Clause4 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) s p : Prop :=
  forall o s', s = (Cons (inr o) s') -> exists o', rel ORel l o' o /\ exists p', reduceO p o' p' /\ R s' p'.


(*Variant Clause4 {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | Clause4F : forall p p' o o' s s', s = (Cons (inr o) s') ->  rel ORel l o o' -> reduceO p o' p' -> R s' p' -> Clause4 l IRel ORel R s p.
*)
Variant SimulationF {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) (R : Stream ([I] + [O]) -> Proc I O -> Prop) : Stream ([I] + [O]) -> Proc I O  -> Prop :=
  | SI s p : Clause1 l IRel ORel R s p ->
             Clause2 l IRel ORel R s p ->
             Clause3 l IRel ORel R s p ->
             Clause4 l IRel ORel R s p ->
             SimulationF l IRel ORel R s p.

Ltac rc := rewrite /Clause1 /Clause2 /Clause3 /Clause4.
Lemma monotone_Clause1 {I O : Ty}  l IRel ORel :  monotone2 (@Clause1 I O l IRel ORel).
Proof.
intro. ssa. rc. eauto.
Qed.

Lemma monotone_Clause2 {I O : Ty}  l IRel ORel :  monotone2 (@Clause2 I O l IRel ORel).
Proof.
  intro. rc. ssa. 
  move: (IN _ H). ssa. eauto.
Qed.

Lemma monotone_Clause3 {I O : Ty}  l IRel ORel :  monotone2 (@Clause3 I O l IRel ORel).
Proof.
  intro. rc. ssa. subst.
  move: (IN _ _ Logic.eq_refl _ H0). ssa. eauto.
Qed.

Lemma monotone_Clause4 {I O : Ty}  l IRel ORel :  monotone2 (@Clause4 I O l IRel ORel).
Proof.
  intro. rc. ssa. subst.
  move: (IN _ _ Logic.eq_refl). ssa. eauto.
  exists x. ssa. eauto.
Qed.


Lemma monotone_SimulationF {I O : Ty}  l IRel ORel :  monotone2 (@SimulationF I O l IRel ORel).
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

Definition simulation {I O : Ty} l IRel ORel s p := paco2 (@SimulationF I O l IRel ORel) bot2 s p.

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
Lemma toNotSim : forall {I O : Ty} (l : level) (IRel : myrel [I]) (ORel : myrel [O]) s (p : Proc I O), NotSim l IRel ORel s p -> ~simulation l IRel ORel s p.
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
  
Section AdmittedTheorems.

Definition NI (I O :Ty) IRel ORel (p : Proc I O) := forall l s, trace s p -> @simulation I O l IRel ORel s p.

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

Definition eqsum (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) : myrel ([Sum I O]).
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


 Theorem sta_NI : forall (I O V : Ty) (p : Proc (Times V I) O) f g v (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O]), NI (eqpair_LR VRel IRel) ORel p -> fv_NI g ORel VRel VRel -> fv_NI f IRel VRel VRel -> equivalence_preserving f IRel VRel -> NI IRel (eqpair VRel ORel) (sta f g v p).
 Admitted.


Definition levelPred := level -> Prop.
 Definition aware (V : Ty) (VRel : myrel [V])  (v : [V]) : levelPred
   := fun l => (forall v', rel VRel l v v' -> v = v') /\ ~ dis VRel l v.

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

(*Definition order_respecting (ls : seq level) :=  forall l l', order l l' -> l \in ls -> l' \in ls.*)

Definition eqmaybe {V : Ty} (VRel : myrel [V]) (P: levelPred) : myrel ([Option V]).
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

Definition aware_or_oblivious  {I O : Ty} (ORel : myrel [O]) (o : [O]) (p : Proc I O) : levelPred := fun l => aware O ORel o l \/ oblivious ORel p l.

Theorem swi_NI : forall (I O : Ty) (IRel : myrel [I]) (ORel : myrel [O]) p b, NI IRel (eqpair_LR boolRel ORel) p ->
 NI (eqpair_LR boolRel IRel) (eqmaybe ORel (fun l => aware Bool boolRel true l \/ oblivious (eqpair_LR boolRel ORel) p l)) (swi b p).
Admitted.


Theorem maybe_NI : forall (I O :Ty) (IRel : myrel [I]) (ORel : myrel [O]) p, NI IRel ORel p -> NI (eqmaybe IRel (fun _ => False)) ORel (maybe p).
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



Definition scheduled_p (I O : Ty) (b : bool) (p : Proc I O) := @map _ _ (Times _ _) _ id snd
                                                                 (@sta (Times Bool _) _ Bool (fun i v => xor (fst i) v) (fun o v => v) b
                                                                 (@map (Times _ (Times _ _))  (Times _ (Times _ _)) _ _ (fun i => (fst (snd i),(fst i,snd (snd i)))) id
                                                                 (swi b (@map (Times Bool _) (Option _) _ (Times Bool _) (fun i => if fst i then Some (snd i) else None) (fun o => (false,o))
                                                                           (maybe p))))).
Check scheduled_p.
Definition par2 (I1 I2 : Ty) (O1 O2 : Ty) (p1 : Proc I1 O1) (p2 : Proc I2 O2) : Proc (Times I1 I2) (Times O1 O2) :=
  par (@map (Times _ _) _ _ _ fst id p1) (@map (Times _ _) _ _ _ snd id p2).

Definition testp (I1 I2 I3 : Ty) (O1 O2 O3 : Ty) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (p3 : Proc I3 O3)  :=
  @sta _ _ (Times Bool (Times Bool Bool)) (fun i v => v) (fun o v => v) (false,(false,false))
    (@map (Times (Times Bool (Times Bool Bool)) (Times _ (Times _ _))) (Times (Times Bool _) (Times (Times Bool _) (Times Bool _))) _ _ (fun i => let:((b1,(b2,b3)),(p1,(p2,p3))) := i in ((b1,p1),((b2,p2),(b3,p3)))) id (par2 (scheduled_p true p1) (par2 (scheduled_p false p2) (scheduled_p false p3)))).

Check testp.
(*Definition par3 (I1 I2 I3 : Ty) (O1 O2 O3 : Ty) (p0 : Proc I1 O1) (p1 : Proc I2 O2) (p2 : Proc I3 O3) := @map _ (Times _ (Times _ _)) _ _ (fun i => (i,(i,i))) id (par (@scheduled_p _ _ false p0) (par (@scheduled_p _ _ false p1) (@scheduled_p _ _ false p2))).
Definition par2 (I1 I2 O1 O2 : Ty) (p1 : Proc I1 O1) (p2 : Proc I2 O2) : Proc (Sum I1 I2) (Sum O1 O2) :=
  @map _ _ _ _ (fun i => (i,i)) par p1 p2

  @map (Times _ _) (Times _ (Times _ _)) (Times _ _) _ (fun i => (fst i,i)) snd (@swi _ _ b ((@map (Times Bool _) (Option _) _ (Times Bool _) (fun i => if fst i then Some (snd i) else None) (fun o => (false,o)) (maybe p)))).

Definition scheduled_p (I O : Ty) (b : bool) (p : Proc I O) : Proc (Times Bool (Option I)) (Option O) :=
  @map (Times _ _) (Times _ (Times _ _)) (Times _ _) _ (fun i => (fst i,i)) snd (@swi _ _ b ((@map (Times Bool _) (Option _) _ (Times Bool _) (fun i => if fst i then Some (snd i) else None) (fun o => (false,o)) (maybe p)))).

Definition par_swiI2 {I1 I2 O1 O2} (b:bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2)
  : Proc (Times Bool (Sum I1 I2)) (Sum O1 O2) :=
    par
      (swi b (@map (Times _ _) _ _ (Times Bool _) fst (fun x => (false,x)) p1))
      (swi (negb b) (@map (Times _ _) _ _ (Times Bool _) snd (fun x => (false,x)) p2)).*)

Lemma par_swiI_NI : forall (I1 I2 O1 O2 : Ty) (b : bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (IRel1 : myrel [I1]) (IRel2 : myrel [I2]) (ORel1 : myrel [O1]) (ORel2 : myrel [O2]),
     NI IRel1 ORel1 p1 -> NI IRel2 ORel2 p2 -> NI (eqpair_LR boolRel (eqpair IRel1 IRel2)) (eqpair (eqmaybe ORel1 (aware Bool boolRel true)) (eqmaybe ORel2 (aware Bool boolRel false))) (par_swiI b p1 p2).
Proof. Admitted.

Definition bool3Type := Times Bool (Times Bool Bool).

Definition proj1 (b : [bool3Type]) : [Bool] := fst b.
Definition proj2 (b : [bool3Type]) : [Bool] := fst (snd b).
Definition proj3 (b : [bool3Type]) : [Bool] := snd (snd b).

Definition bool1 : [bool3Type] := (true,(false,false)).
Definition bool2 : [bool3Type] := (false,(true,false)).
Definition bool3 : [bool3Type] := (false,(false,true)).


(*sta_swi b n f p:
 (i == n,I') -> enables p
 (i <> n,I') -> disables p
 f projects input from pair e.g. f (I1,I2) = I1*)
Definition sta_swi (I' I O : Ty) (b : bool) (n : nat) (f : [I'] -> [I]) (p : Proc I O) :=
@map (Times Nat _) (Times Bool _) (Times _ _) _ (fun x => (fst x == n,snd x)) snd
  (@sta (Times Bool _) _ Bool
       (fun i v => xor (fst i) v)
       (fun o v => false)
       b
       ( @map (Times Bool (Times Bool _)) (Times Bool _) _ _
          (fun i => (fst i,snd (snd i)))
          id
          (swi b (@map _ _ _ (Times Bool _)
                    f
                    (fun o => (true,o))
                    (p)
  )))).

Definition par_swiI3 {I1 I2 I3 O1 O2 O3} (n : nat) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (p3 : Proc I3 O3)
  : Proc (Times Nat (Times I1 (Times I2 I3))) (Times (Option O1) (Times (Option O2) (Option O3))) :=
    par
      (@sta_swi (Times _ _) _ O1 (n == 0) 0 fst p1)
      (par
      (@sta_swi (Times _ (Times _ _)) _ O2 (n == 1) 1 (fun x => fst (snd x)) p2)
      ((@sta_swi (Times _ (Times _ _)) _ O3 (n == 2) 2 (fun x => snd (snd x)) p3))). 




(*Definition par_swiI3 {I1 I2 I3 O1 O2 O3} (n : nat) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (p3 : Proc I3 O3)
  : Proc (Times TNat (Times I1 (Times I2 I3))) (Times (Option O1) (Times (Option O2) (Option O3))) :=
    par
      (@map (Times TNat _) (Times Bool _) _ _ (fun x => (fst x == 0,snd x)) id (@sta_swi (Times _ _) _ O1 (n == 0) fst p1))
      (par
      (@map (Times TNat _) (Times Bool _) _ _ (fun x => (fst x == 1,snd x)) id (@sta_swi (Times _ (Times _ _)) _ O2 (n == 1) (fun x => fst (snd x)) p2))
      (@map (Times TNat _) (Times Bool _) _ _ (fun x => (fst x == 2,snd x)) id (@sta_swi (Times _ (Times _ _)) _ O3 (n == 2) (fun x => snd (snd x)) p3))).*) 


(*Definition par_swiI3 {I1 I2 I3 O1 O2 O3} (n : nat) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (p3 : Proc I3 O3)
  : Proc (Times TNat (Times I1 (Times I2 I3))) (Times (Option O1) (Times (Option O2) (Option O3))) :=
    par
      (@map (Times TNat _) (Times Bool _) _ _ (fun x => (fst x == 0,snd x)) id (swi (n == 0) (@map (Times _ _) _ _ (Times Bool _) fst (fun x => (true,x)) p1)))
      (par
      (@map (Times TNat _) (Times Bool _) _ _ (fun x => (fst x == 1,snd x)) id (swi (n == 1) (@map (Times _ (Times _ _)) _ _ (Times Bool _) (fun x => fst (snd x)) (fun x => (true,x)) p2)))
      (@map (Times TNat _) (Times Bool _) _ _ (fun x => (fst x == 2,snd x)) id (swi (n == 2) (@map (Times _ (Times _ _)) _ _ (Times Bool _) (fun x => snd (snd x)) (fun x => (true,x)) p3)))).*)


(*Definition par_swiI3 {I1 I2 I3 O1 O2 O3} (b : [bool3Type]) (p1 : Proc I1 O1) (p2 : Proc I2 O2) (p3 : Proc I3 O3)
  : Proc (Times bool3Type (Times I1 (Times I2 I3))) (Times (Option O1) (Times (Option O2) (Option O3))) :=
    par
      (@map (Times bool3Type _) (Times Bool _) _ _ (fun x => (proj1 (fst x),snd x)) id (swi (proj1 b) (@map (Times _ _) _ _ (Times Bool _) fst (fun x => (false,x)) p1)))
      (par
      (@map (Times bool3Type _) (Times Bool _) _ _ (fun x => (proj2 (fst x),snd x)) id (swi (proj2 b) (@map (Times _ (Times _ _)) _ _ (Times Bool _) (fun x => fst (snd x)) (fun x => (false,x)) p2)))
      (@map (Times bool3Type _) (Times Bool _) _ _ (fun x => (proj3 (fst x),snd x)) id (swi (proj3 b) (@map (Times _ (Times _ _)) _ _ (Times Bool _) (fun x => snd (snd x)) (fun x => (false,x)) p3)))).
*)



Ltac rewr := idtac. (*updated later*)

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

Ltac reduce_tac :=
  (try rewr);
   (repeat
      reduce_once);(try swi_instans);controlled_eauto; rewrite ?eqxx /= /xor /=.

Ltac reduce_tac_v :=
  (try rewr);(rewrite ?eqxx /= /xor /= );
   repeat first [reduce_once_v;first try econ | swi_instans].
(*Ltac reduce_tac' :=
  (try rewr);
   (repeat
      reduce_once);(try swi_instans); rewrite ?eqxx /= /xor /=.*)

(*Ltac reduce_tac_ne :=
  (try rewr);
   (repeat
    reduce_once);(try swi_instans);rewrite ?eqxx /= /xor /=.*)


Ltac appTrace := apply: traceI || apply: traceO.


Ltac bundle :=
  (pfold;
  first [ appTrace | rewr;appTrace ];
   first (do ? reduce_tac));controlled_eauto;simpl.

Ltac bundle_v :=
  (pfold;
  first [ appTrace | rewr;appTrace ];
  first (do ? reduce_tac_v));simpl;try econ.

Ltac check_if_var x :=
  first [ is_var x;fail 1 "Term" x "is not a bare variable" | idtac ].

(*Ltac match_dd := 
   repeat
    match goal with
    | H : reduceI ?p _ _ |- _ => dependent destruction  H
    | H : reduceO ?p _ _ |- _ => dependent destruction  H
    end.*)

Ltac match_dd := 
   repeat
    match goal with
    | H : reduceI ?p _ _ |- _ => check_if_var p; dependent destruction  H
    | H : reduceO ?p _ _ |- _ => check_if_var p; dependent destruction  H
    end.


(*Types used in all examples*)
Definition ExInputType := Times TInput TInput.
Definition ExOutputType := Times (Option TOutput) (Option TOutput).

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

Definition Output_option : myrel ([Option TOutput]) := eqmaybe OutputRel (fun l => l = \top).

Definition Output_option_prod : myrel ([ExOutputType]).
  apply eqpair. apply Output_option. apply Output_option.
  Defined.


Module Example1.
(*Process*)
Definition p1_simple := @out TInput TOutput Step.
Definition p2 := @out TInput TOutput Idle.
Definition processes_simple := par_swiI false p1_simple p2.
Definition leaking_scheduler := @map _ (Times Bool (Times TInput TInput)) _ _ (fun (i : [TInput]) => (i == DiskRead,(i,i))) id processes_simple.


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
Ltac rewr ::=  (try rewrite newtrace_simple_eq); rewrite /newtraceF_simple /processes_simple /par_swiI /leaking_scheduler /p1_simple /p2.
Lemma simple_trace : trace newtrace_simple leaking_scheduler.
Proof.
  pcofix CIH.
  rewr.
  bundle. left.
  bundle. left.
  bundle. right.
  swi_instans. eauto.
Qed.

(*NotSim*)
Example counterexample : NotSim \bot InputRel Output_option_prod newtrace_simple leaking_scheduler.
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
Example example_not_NI :  ~ NI InputRel Output_option_prod leaking_scheduler.
Proof.
  rewrite /NI. ssa. intro.
  Search _ NotSim.
  apply/toNotSim. apply/counterexample.
  apply/H. apply simple_trace.
Qed.

End Example1.


Module Example2.
(*high low*)

Definition naive_scheduler {I O} (p : Proc (Times Bool (Times I I)) O) : Proc I O :=
  @map _ (Times Bool (Times _ _)) _ _ (fun i => (true,(i,i))) id p.

Definition hp_lp := naive_scheduler (par_swiI true (@out TInput TOutput Idle) (@out TInput TOutput Step)).

Definition InputRelPublic : myrel ([TInput]). 
  refine (@MyRel _
            (fun l a => False)
            (fun l a b => a = b) _ _ _ _).
  intros.
  done.
  intros. done.
  intros. subst. done.
Defined.

Definition TraceF_specific := (@TraceF TInput (Times (Option TOutput) (Option TOutput))).
Lemma specific_monotone : monotone2 TraceF_specific.
  apply (@monotone_TraceF TInput (Times (Option TOutput) (Option TOutput))).
Qed.

Hint Resolve specific_monotone : paco.
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


Arguments NI : clear implicits.
Arguments NI I O [_] [_].
Example hl_lp_NI : @NI _ _ InputRelPublic Output_option_prod hp_lp.
Proof.
  rewrite /hp_lp /naive_scheduler.
  eapply map_NI.
  eapply par_swiI_NI.
  apply out_NI.
  apply out_NI.

  instantiate (1:= (InputRelPublic)).
  instantiate (1:= (InputRelPublic)).  
  rewrite /f_NI. ssa.

  rewrite /f_PU. ssa.

  instantiate (1:= OutputRel).
  instantiate (1:= OutputRel).

  ssa.
Qed.

End Example2.

Section Example3.
(*high process: out InternalStep *)

(*Definition SimpleTypeRel (t : Ty): myrel [t].
    refine (@MyRel _ 
            (fun (l : level) _ => False)
            (fun l io1 io2 => io1 = io2)
                        _
            _
            _
            _).
  - intros. done.
  - intros. done.
  - done.
Defined.*)

(*Definition collapse_opair (A : Set) (o : option A * (option A)) (d : A) :=
  match o with
  | (Some o', _) => o'
  | (_, Some o') => o'
  | _ => d
  end.*)

(*Definition alternate (I O : Ty) (o1 o2 : [O]) := @map I _ (Times Nat _) _ id (fun o => if ((fst o) %% 2 == 1) then o1 else o2 )(@sta _ _ Nat (fun i v => v) (fun o v => (v+1)%%2) 0 (@out (Times Nat I) Unit tt)).*)

  
Definition low_p := @out TInput TPublicOutput GetRequest.
Definition high_p := @out THandlerOutput TTypeSyscall Syscall. Check sta.

(*Got complicated because we need to do 2 things:
1) Distinguish what we output based on whether an input has happened since the last output
2) reset the state after the output has performed

in sta, the state cannot be expected during creation of output, resetting the state therefore removes the information we would need to distinguish states.
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

Definition InputType := (Times (Option TInput) (Times (Option THandlerOutput) (Option TInterrupt))).

Definition NInputType := Times Nat InputType.
Definition OutputType :=  (Times (Option TPublicOutput) (Times (Option TTypeSyscall) (Option THandlerOutput))).

Definition IOType := Sum InputType OutputType. 

(*Definition mytest := par_swiI3 0 (maybe p1_simple) (maybe high_p) (maybe handler).
Check mytest. Print HandlerOutput. Check high_p.*)

Definition process_pool := par_swiI3 0 (maybe low_p) (maybe high_p) (maybe handler).


Definition myvT := Times Bool (Times Nat Nat).

Definition inc_myv (v : [myvT]) :=
  let: (b,(c,n)) := v in if b then v else if c == 0 then (b,(c+1,n)) else (b,(0,(n+1)%%2)). (* low process: n = 0 and (b = false)
                                                                                               high process: n = 1 and (b = false)
                                                                                               handler: b = true
                                                                                               two steps per low/high process counted by (c), with c == 0 meaning has the first step been taken yet
                                                                                               nat used for c instead of bool both for readability and in case we increase step count for examples in the future*)

Definition myv_to_n (v: [myvT]) : nat :=
  let: (b,(c,n)) := v in if b then 2 else n. (*mapping state myvT to the process that should be scheduled*)

Definition handler_up_v (o : [IOType]) (v: [myvT])  : [myvT] := (*based on output and state, schedule/deschedule handler using the bool flag*)
  let: (b,(c,n)) := v in
  match b,o with
  | false,inl (None,(None, Some i)) => (true,(c,n))
  | true, inr (None,(None, Some Notify)) => (false,(c,n))
  | _,_ => v
  end.

(*Definition bad_scheduler := loop (@map _ _ (Times _ _) _ id snd (@sta _ _ myvT handler_up_v (fun o v => inc_myv v) (false,(0,0)) (@map (Times myvT _) (Times Nat _) _ _ (fun x => (myv_to_n (fst x), snd x)) id process2))).*)

Definition bad_scheduler (p : Proc NInputType OutputType)  :=
  @map InputType IOType IOType OutputType
    inl
    (fun x => match x with | inl _ => (None,(None,None)) | inr y => y end)
    (loop (*scheduler needs loop - We can only switch par_swiI3 on input, thus output rerouted as input allows scheduler to count outputs - Outputs is our unit of time*)
       (@map _ _ (Times _ _) _
          id
          snd (*removes state*)
          (@sta _ _ myvT
             handler_up_v
             (fun o v => inc_myv v)
             (false,(0,0))
             (@map (Times myvT IOType) NInputType OutputType IOType
                (fun x => let n := myv_to_n (fst x) in (*map *)
                          match snd x with
                          | inl i' => (n,i') (*inl = input*)
                          | inr (None,(None,Some h)) => (n,(None,(Some h,None))) (*inr = output from handler rerouted as input to high process *)
                          | inr _ => (n,(None,(None,None))) (*inr = output that is discarded, but n is used to ac*)
                          end)
                inr
                p
    )))).

(*
Definition bad_scheduler (p : Proc (Times Nat IOType) IOType)  :=
  @map InputType IOType IOType OutputType
    inl
    (fun x => match x with | inl _ => (None,(None,None)) | inr y => y end)
    (loop
       (@map _ _ (Times _ _) _
          id
          snd (*removes state*)
          (@sta _ _ myvT
             handler_up_v
             (fun o v => inc_myv v)
             (false,(0,0))
             (@map (Times myvT _) (Times Nat _) _ _
                (fun x => (myv_to_n (fst x), snd x))
                id
                p
    )))).*)

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

Ltac rewr ::=  (try rewrite ex3_stream_eq); rewrite /par_swiI /bad_scheduler /process_pool /low_p  /ex3_streamF /bad_scheduler /process_pool /par_swiI3 /high_p /handler /sta_swi.


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



Definition InputTypeRel : myrel [InputType].
  rewrite /InputType. 
  refine (@MyRel _ 
            (fun (l : level) v => if l == \bot then match v with | (_,(None,None)) => False | _ => True end else False)
            (fun l io1 io2 => io1 = io2)
            _
            _
            _
            _).
  - by intros.
  - intros. rewrite /order in H. destruct (eqVneq l1 \bot). subst. rewrite lex0 in H. rewrite (eqP H) eqxx.
    de a. done.
  - intros. subst. destruct (eqVneq l \bot). subst. de a1. done.
Defined.

Definition OutputTypeRel : myrel [OutputType].
  rewrite /OutputType.
  refine (@MyRel _ 
            (fun (l : level) v => if l == \bot then match v with | (_,(Some NPublic,Some SPublic)) => False | _ => True end else False)
            (fun l io1 io2 => io1 = io2)
            _
            _
            _
            _).
  - by intros. 
  - intros. rewrite /order in H. destruct (eqVneq l1 \bot). subst. rewrite lex0 in H. rewrite (eqP H) eqxx.
    de a. done.
  - intros. subst. destruct (eqVneq l \bot). subst. de a1. done.
Defined.

Ltac dd H := dependent destruction H.

Ltac temp_match := 
    match goal with
    | H : reduceI ?p _ _ |- _ =>  check_if_var p;  dependent destruction  H
    | H : reduceO ?p _ _ |- _ => check_if_var p; dependent destruction  H
    end.

Example counterexample : NotSim \bot InputTypeRel OutputTypeRel ex3_stream (bad_scheduler process_pool).
Proof.
  apply: NS2.
  instantiate (1:= (None,(None,(Some TimerInterrupt)))). ssa. rewrite eqxx //.

  move=>p'. rewr. ssa.
  match_dd.
  apply:NS4.
  ssa.
  match_dd.
Qed.  

Example example_not_NI : ~ @NI _ _ InputTypeRel OutputTypeRel (bad_scheduler process_pool).
Proof.
  rewrite /NI. ssa. intro.
  apply/toNotSim. apply/counterexample.
  apply/H. apply simple_trace.
Qed.  

End Example3.










Example ex3_is_bad : NotSim \bot InputTypeRel OutputTypeRel ex3_stream (bad_scheduler process_pool).
Proof.
  apply: NS2.
  instantiate (1:= (None,(None,(Some TimerInterrupt)))). ssa. rewrite eqxx //.
  move=> p' Hred. match_dd
                                                                                                      match_dd_safe.
  dd H0. de o.
  dd H1.
  dd H1. dd H1.
  dd H



Definition LoopRel : myrel [IOType].
  apply eqsum. apply InputTypeRel. apply OutputTypeRel.
Defined.


(*I think this might not be true*)
Example bad_scheduler_is_bad : NotSim \bot Ex3InputRel OutputTypeRel ex3_stream (bad_scheduler process_pool).
Proof. 
  rewrite ex3_stream_eq /ex3_streamF.
(*  apply: NS2. instantiate (1:= (DiskRead)).
  rewrite /= eqxx. auto.

  intros. match_dd.

  apply: NS3. ssa. de x. subst.
  match_dd.
  
  apply: NS4. ssa. de o'. subst.
  match_dd.*)
Abort.

Lemma stays_i : forall i, reduceI (bad_scheduler process_pool) i (bad_scheduler process_pool).
Proof.
  intros.
  rewr.
  reduce_tac.
  destruct i. ssa. destruct i.
  reduce_once. reduce_once.
  reduce_once.
  reduce_tac.
  de i. de i0. de o. reduce_tac.
  de i. de i0. de o0. reduce_tac.
Qed.

(*Lemma stays_i2 : forall p i, reduceO (bad_scheduler process_pool) (Some Step,(None,None)) p -> reduceI p i p.
Proof.
  intros.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.  
  dependent destruction H0.
  dependent destruction H0.
  dependent destruction H0.
  dependent destruction H.
  dependent destruction H1.
  dependent destruction H1.
  dependent destruction H1.
  ssa. subst.

  reduce_tac.
  dependent destruction H0;eauto.

  dd H0_0. dd H0_0_1.
  dd H0_. dd H0_0.
  
  dependent destruction H1.
  reduce_tac.
  
  dependent destruction H1_. done.
  reduce_tac. ssa.
  2:ssa.
  move: H. rewr.
  match_dd.
  rewr.
  reduce_tac.
  destruct i. ssa. destruct i.
  reduce_once. reduce_once.
  reduce_once.
  reduce_tac.
  de i. de i0. de o. reduce_tac.
  de i. de i0. de o0. reduce_tac.
Qed.*)

Definition p22 :=
       ((@map InputType IOType IOType OutputType
       (@inl (option Input * (option TypeSyscall * option TypeSyscall))
          (option Output * (option TypeSyscall * option TypeSyscall)))
       (fun
          x : option Input * (option TypeSyscall * option TypeSyscall) +
              option Output * (option TypeSyscall * option TypeSyscall) =>
        match x with
        | @inl _ _ _ => (@None Output, (@None TypeSyscall, @None TypeSyscall))
        | @inr _ _ y => y
        end)
       (@loop IOType
          (@map IOType IOType (Times myvT IOType) IOType id
             (@snd (bool * (nat * nat))
                (option Input * (option TypeSyscall * option TypeSyscall) +
                 option Output * (option TypeSyscall * option TypeSyscall)))
             (@sta IOType IOType myvT handler_up_v (fun=> [eta inc_myv])
                (false, (0 + 1, 0))
                (@map (Times myvT IOType) (Times Nat IOType) IOType
                   IOType
                   (fun
                      x : bool * (nat * nat) *
                          (option Input * (option TypeSyscall * option TypeSyscall) +
                           option Output * (option TypeSyscall * option TypeSyscall)) =>
                    (myv_to_n x.1, x.2))
                   id
                   (@map (Times Nat IOType) NInputType OutputType IOType
                      (fun
                         i0 : nat *
                              (option Input * (option TypeSyscall * option TypeSyscall) +
                               option Output * (option TypeSyscall * option TypeSyscall)) =>
                       let (n, i1) := i0 in
                       match i1 with
                       | @inl _ _ i' => (3, i')
                       | @inr _ _ _ => (n, (@None Input, (@None TypeSyscall, @None TypeSyscall)))
                       end)
                      (@inr (option Input * (option TypeSyscall * option TypeSyscall))
                         (option Output * (option TypeSyscall * option TypeSyscall)))
                      (@par NInputType (Option TOutput)
                         (Times (Option TTypeSyscall) (Option TTypeSyscall))
                         (@map NInputType
                            (Times Bool
                               (Times (Option TInput)
                                  (Times (Option TTypeSyscall) (Option TTypeSyscall))))
                            (Option TOutput) (Option TOutput)
                            (fun x : nat * (option Input * (option TypeSyscall * option TypeSyscall)) =>
                             (x.1 == 0, x.2))
                            id
                            (@swi
                               (Times (Option TInput)
                                  (Times (Option TTypeSyscall) (Option TTypeSyscall)))
                               TOutput true
                               (@map
                                  (Times (Option TInput)
                                     (Times (Option TTypeSyscall) (Option TTypeSyscall)))
                                  (Option TInput) TOutput (Times Bool TOutput)
                                  (@fst (option Input) (option TypeSyscall * option TypeSyscall))
                                  [eta @pair bool Output true]
                                  (@maybe TInput TOutput (@out TInput TOutput Step)))))
                         (@par NInputType (Option TTypeSyscall) (Option TTypeSyscall)
                            (@map NInputType
                               (Times Bool
                                  (Times (Option TInput)
                                     (Times (Option TTypeSyscall) (Option TTypeSyscall))))
                               (Option TTypeSyscall) (Option TTypeSyscall)
                               (fun
                                  x : nat *
                                      (option Input * (option TypeSyscall * option TypeSyscall)) =>
                                (x.1 == 1, x.2))
                               id
                               (@swi
                                  (Times (Option TInput)
                                     (Times (Option TTypeSyscall) (Option TTypeSyscall)))
                                  TTypeSyscall false
                                  (@map
                                     (Times (Option TInput)
                                        (Times (Option TTypeSyscall) (Option TTypeSyscall)))
                                     (Option TTypeSyscall) TTypeSyscall (Times Bool TTypeSyscall)
                                     (fun
                                        x : option Input * (option TypeSyscall * option TypeSyscall) =>
                                      x.2.1)
                                     [eta @pair bool TypeSyscall true]
                                     (@maybe TTypeSyscall TTypeSyscall
                                        (@map TTypeSyscall TTypeSyscall (Times Nat Unit) TTypeSyscall
                                           id
                                           (fun o : nat * unit =>
                                            if o.1 %% 2 == 1 then Syscall else InternalStep)
                                           (@sta TTypeSyscall Unit Nat (fun=> id)
                                              (fun=> (fun v : nat => (v + 1) %% 2)) 0
                                              (@out (Times Nat TTypeSyscall) Unit tt)))))))
                            (@map NInputType
                               (Times Bool
                                  (Times (Option TInput)
                                     (Times (Option TTypeSyscall) (Option TTypeSyscall))))
                               (Option TTypeSyscall) (Option TTypeSyscall)
                               (fun
                                  x : nat *
                                      (option Input * (option TypeSyscall * option TypeSyscall)) =>
                                (x.1 == 2, x.2))
                               id
                               (@swi
                                  (Times (Option TInput)
                                     (Times (Option TTypeSyscall) (Option TTypeSyscall)))
                                  TTypeSyscall false
                                  (@map
                                     (Times (Option TInput)
                                        (Times (Option TTypeSyscall) (Option TTypeSyscall)))
                                     (Option TTypeSyscall) TTypeSyscall (Times Bool TTypeSyscall)
                                     (fun
                                        x : option Input * (option TypeSyscall * option TypeSyscall) =>
                                      x.2.2)
                                     [eta @pair bool TypeSyscall true]
                                     (@maybe TTypeSyscall TTypeSyscall
                                        (@map TTypeSyscall TTypeSyscall (Times Nat Unit) TTypeSyscall
                                           id
                                           (fun o : nat * unit =>
                                            if o.1 %% 2 == 1 then InternalStep else Notify)
                                           (@sta TTypeSyscall Unit Nat (fun=> id)
                                              (fun=> (fun v : nat => (v + 1) %% 2)) 0
                                              (@out (Times Nat TTypeSyscall) Unit tt)))))))))))))))).

Lemma p22_stays : forall i, reduceI p22 i p22.
Proof.
  case.
  case. move=> a [].
  move=> a0 b.
  rewrite /p22.
  reduce_tac;reduce_tac.
  de a0.
  reduce_tac.
  de b.
  reduce_tac.
  case. case. move=> a [].
  move=> a0. rewrite /p22.
  reduce_tac;reduce_tac.
  rewrite /p22. reduce_tac;reduce_tac.
  case. move=> a. rewrite /p22.
  reduce_tac;reduce_tac.
  rewrite /p22. reduce_tac;reduce_tac.
Qed.  
Example bad_scheduler_is_good : simulation \bot Ex3InputRel OutputTypeRel ex3_stream (bad_scheduler process_pool).
Proof.
pcofix CIH.  
pfold. con;
  [rewrite /Clause1;ssa;rewrite ex3_stream_eq in H;inv H | idtac | rewrite /Clause3;ssa;rewrite ex3_stream_eq  in H;inv H | idtac] .

rewrite /Clause2;ssa;econ;
con;last (right;apply:CIH);
rewr;de i;reduce_tac;
    [ de o;reduce_tac |
      de p;reduce_tac;de o0;reduce_tac |
      de p;reduce_tac; de o1;reduce_tac ]. 

rewrite /Clause4; ssa;rewrite ex3_stream_eq in H;inv H.
econ. con. eauto. econ. con.
rewr. reduce_tac. econ. eauto.
2: eauto. 2:eauto. 2: { eauto.
- rewrite /Clause3;ssa;rewrite ex3_stream_eq  in H;inv H.
- rewrite /Clause4. ssa. rewrite ex3_stream_eq in H. inv H.
  (*continuing case 4*)
  exists ((Some Step,(None,None))). ssa. econ. econ.
  reduce_tac;try econ. econ.
  reduce_tac. econ.
  reduce_tac. reduce_tac. econ.
  do ? reduce_tac. econ.
  reduce_tac. reduce_tac.

  (*trace and process consumed insert1 Step*)
  left. pcofix CIH2. pfold. con.
     - rewrite /Clause1. ssa.
     - rewrite /Clause2. de i.
     1 : { 
     de i. de i0. de o. de o0. econ. con.
     reduce_tac.
     reduce_tac.
     reduce_tac.
     reduce_tac. right. ssa. eauto.
     left.
     swi_instans.
     Set Printing Implicit.





  ssa. rewrite eqxx in H0.
  
2: { rewrite /Clause2. ssa. rewriite 
- rewrite /Clause1. ssa. rewrite eqxx in H0. de i. de p. de o0. 
  left. pfold.
  







































































(*Definition process3   := @sta _ _ Nat (fun i v => v)  0
                                                   (@loop (Times Nat LoopType) (@map (Times Nat LoopType) Ex3NInput OutputType (Times Nat LoopType) (fun i => match i with | (n,inl i') => (n %/ 2,i') | (n,inr o) => (n %/ 2,d) end) (fun x => (0, inr x)) par_proc )).*)



Definition new_scheduler (I1 I2 I3 O1 O2 O3: Ty)
  (p : Proc (Times Bool (Times I1 (Times I2 I3))) (Times (Option O1) (Times (Option O2) (Option O3))))
  := @sta _ _ (Times bool3Type TNat) (fun i v => v) (fun o v => (if snd v %% 5 == 0 then inc_bool (fst v) else fst v,(snd v) %/ 5)) ((false,(false,false)),0) (@map (Times _ _) _ _ _ snd id (p)).
  
           

(*L | H | handler*)
(*TInput | TInput | TTypeSyscall*)
(*Proc A B | Proc C D | Proc D C*)

Definition inc_bool (b : [bool3Type]) :=
  match b with
  | (false,(false,false)) => (true,(false,false))    
  | (true,(false,false)) => (true,(true,false))
  | (true,(true,false)) => (false,(true,true))
  | (false,(true,true)) => (true,(false,true))
  | (true,(false,true)) => (true,(true,false))                             
  | _ => (true,(false,false))
  end.

(*Definition new_o := @par _ _ _ p1_simple (@par _ _ (Times (Option _) (Option _)) high_p handler).*)

              

                       
  Definition process3 := tt.



End Example3.    





                   
Ltac trace_tac := 
   repeat
    match goal with
    | H : monotone2 (Stream (sum ?i ?o)) TraceF  |- _ => dependent destruction  H
    | H : reduceO _ _ _ |- _ => dependent destruction  H
    end.                   

Print newtraceF_simple.
Example counterexample_notsim : ~ simulation \bot InputRel Output_option_prod newtrace_simple leaking_scheduler.
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
