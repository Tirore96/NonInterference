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
Require Import Stdlib.Program.Equality.
From Equations Require Import Equations.
Require Import Stdlib.Classes.DecidableClass.
From Stdlib Require Eqdep.

Import Order.TTheory.
Open Scope order_scope.

Require Import NonInterference.theorems.
Require Import NonInterference.current_files.current.

Lemma test_step1 : Trace (eqpair_LR (eqmaybe (publicRel (Times Nat Bool)))
                          (eqpair_LR (eqmaybe (publicRel TPublicOutput))
                             (eqpair_LR (eqmaybe (semiprivateRel TTypeSyscall))
                                 (eqmaybe (semiprivateRel THandlerOutput))))) false badtrace' my_only_loop_bad'.
Proof.
  rewrite /badtrace'.
  eapply TR1.
  reduce_tac; repeat (reduce_once || econ).
  match goal with | |- ?G => fail 1 G end.
Admitted.
