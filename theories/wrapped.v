
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

Require Export NonInterference.process.

Definition T_out := Option (Sum TPublicOutput TTypeSyscall).

Definition parse_output (o : [T_out']) : [T_out] :=
  match o with
  | (Some public,_) => Some (inl public)
  | (None,(Some prv,_)) => Some (inr prv)
  | _ => None
  end.

Definition final_out_rel : myrel [T_out] := eqmaybe_false (eqsum (publicRel _) (semiprivateRel _)).

Definition wrapped_model_good : Proc T_in T_out := map id parse_output model_good.

Lemma wrapped_model_good_NI : NI in_rel final_out_rel wrapped_model_good.
Proof.
  eapply map_NI. eauto. eauto.
  2: apply model_good_NI.
  mrw. intros.
  move: H=> /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + +.
  move: i=>[a[] b[] c[] d[] e f].
  move: i'=>[a'[] b'[] c'[] d'[] e' f']. 
  rewrite !pair_rewr.
  rewrite /parse_output.
  move/rel_eqmaybe2. case.
  move=>[]x'[]y'[]->[]->/publicRel_eq->//.
  move=>[]->->.
  move/rel_eqmaybe2. case.
  move=>[]x'[]y'[]->[]-> H _ _ _ _.
  apply rel_eqmaybe. ssa.
  move=>[]->[]->. auto.
Qed.  
  




  
