
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

Require Import NonInterference.process.

Definition interrupt_rel : myrel [TInterrupt].
  refine (@MyRel _
            (fun l (b : [TInterrupt]) => b = DiskInterrupt /\ l = \bot)
            (fun l b1 b2 => b1 = b2)
            _
            _
            _
            _).
  ssa. ssa. ssa. rewrite /order in H. subst. rewrite lex0 in H. apply/eqP. done.
  ssa. subst. con. ssa. ssa.
Defined.

Definition input_rel' := eqsum_R (publicRel Unit) interrupt_rel.

Lemma NI_model' : NI input_rel' output_rel' model'.
Admitted.
