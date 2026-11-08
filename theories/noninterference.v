
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import RelationClasses.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
From HB Require Import structures.
From deriving Require Import deriving.
Require Import Coq.Classes.DecidableClass.
Import Order.TTheory.
Open Scope order_scope.

Require Export NonInterference.theories.model_immediate.
Require Export NonInterference.theories.model_sliced.
Require Export NonInterference.theories.model_timer_unmasked.

(* ===================================================================
   NonInterference: the concrete security equivalences and the results.

   Paper: Sections IV and V.  Structure:
     4. The model's equivalences : in_equiv, out_equiv (out_equiv_userview is in generic_model.v)
     5. model_immediate_concrete is not non-interfering        (model_immediate_not_NI),
        nor is its user view                          (model_immediate_userview_not_NI),
        nor even its public view                      (model_immediate_publicview_not_NI)
     6. model_sliced / wrapped are non-interfering (model_sliced_NI, model_sliced_userview_NI)
     7. The state equivalence (state_type_equiv) and the fv_NI obligation
   =================================================================== *)

(* --- Section 4: the input equivalence.  An interrupt is a sum (generic_model.v,
   T_in), classified like the current pid: the disk interrupt (inl) is secret,
   unobservable at bot only; the timer interrupt (inr) is public.  (Paper,
   Section IV-A.) --- *)
Definition in_equiv : cEquiv [T_in] := eqsum_L (private_equiv Unit) (public_equiv Unit).

(* The earlier, hand-written definition on the two-constructor interrupt type,
   kept to show that the sum is the same equivalence: ir_dis makes ONLY the
   disk interrupt secret, and only at bot. *)
Definition ir_dis (l : level) (ir : [TInterrupt]) := ir = DiskInterrupt /\ l = \bot.
Definition in_equiv_interrupt : cEquiv [TInterrupt].
  refine (@CEquiv _
            ir_dis
            (fun l ir ir' => ir = ir' \/ ir_dis l ir /\ ir_dis l ir')
            _
            _
            _
            _).
  ssa. con. intro. ssa. intro. ssa. de H.
  intro. ssa. de H. de H0. subst. ssa. subst.
  eauto. de H0. subst. ssa.
  ssa. de H0. eauto. move: H0 H1. rewrite /ir_dis. ssa.
  subst. eauto.
  ssa. move: H0. rewrite /ir_dis. ssa. subst.
  rewrite /order in H. rewrite lex0 in H. apply/eqP. done.
  ssa. rewrite /ir_dis. con. ssa. ssa. de H0. subst.
  move:H. rewrite /ir_dis. intros;subst. ssa.
  ssa. de H0. move: H. rewrite /ir_dis. ssa.
Defined.

Definition interrupt_to_sum (ir : [TInterrupt]) : [T_in] :=
  if ir is DiskInterrupt then inl tt else inr tt.

Lemma interrupt_to_sumK : cancel interrupt_to_sum interrupt_of.
Proof. by case. Qed.

Lemma interrupt_ofK : cancel interrupt_of interrupt_to_sum.
Proof. by case=> [[]|[]]. Qed.

Lemma in_equiv_interrupt_rel l i i' :
  rel in_equiv_interrupt l i i' <-> rel in_equiv l (interrupt_to_sum i) (interrupt_to_sum i').
Proof.
rewrite /in_equiv_interrupt /in_equiv /ir_dis /=.
case: i; case: i' => /=.
- split=> _; last by left.
  by case: (eqVneq l \bot) => [->|/eqP ?]; [right | left].
- by split=> //; case=> [|[_ []]].
- by split=> //; case=> [|[[]]].
- by split=> _ //; left.
Qed.

Lemma in_equiv_interrupt_dis l i :
  dis in_equiv_interrupt l i <-> dis in_equiv l (interrupt_to_sum i).
Proof.
rewrite /in_equiv_interrupt /in_equiv /ir_dis /=; case: i => /=.
- by split; [case | move=> ->].
- by split; [case | ].
Qed.


(* out_equiv: the 6-slot pool output.  Handler slots are NOP, disk,
   timer: the first two are secret (eqmaybe_nonbot private_equiv), the timer slot
   is public (it reacts only to public timer interrupts). *)
Definition out_equiv (Opub Opriv : Ty) : cEquiv [T_out Opub Opriv] := eqpair (eqmaybe_all (public_equiv _))
                                          (eqpair (eqmaybe_all (private_equiv _))
                                             (eqpair (eqmaybe_all (public_equiv _))
                                                (eqpair (eqmaybe_nonbot ((private_equiv _)))
                                                   (eqpair (eqmaybe_nonbot (private_equiv _))
                                                      (eqmaybe_all (public_equiv _)))))).

(* The alphabets the concrete models are instantiated at. *)
Notation out_equiv_concrete := (out_equiv TPublicOutput TTypeSyscall).
Notation out_equiv_userviewC := (out_equiv_userview TPublicOutput TTypeSyscall).

Lemma Trace_imp : forall (A B : Ty) (p : Proc A B) (s : seq ([A] + [B])) l (BRel BRel' : cEquiv [B]), (forall x y, rel BRel l x y -> rel BRel' l x y) -> Trace BRel l s p -> Trace BRel' l s p.
Proof.  
  intros.
  elim : H0 H;ssa.
  econ. eauto. eauto.
  econ;eauto.
Qed.

Lemma helper_trace' : Trace (public_equiv _) \bot [::out_get';out_get'] model_immediate_concrete.
Proof.
    rewrite /model_immediate_concrete /model_immediate.
    rewr;simpl;rewr;simpl;rewr;simpl;rewr.
    (first [econ;[idtac | econ | idtac] | econ];
     reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans).
    simpl.

   (first [econ;[idtac | econ | idtac] | econ];
    reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans).
   econ. reduce_tac2;reduce_tac2. econ. econ. reduce_tac. econ. econ.
   reduce_tac. econ. econ. reduce_tac. econ. econ. reduce_tac. econ.
   econ. reduce_tac. econ. econ. reduce_tac. econ.
Qed.   

Lemma helper_trace : Trace out_equiv_concrete \bot [::out_get';out_get'] model_immediate_concrete.
Proof.
  eapply Trace_imp. 2:eapply helper_trace'.
  intros. simpl in H. subst. auto.
Qed.

(* The same two public requests, seen through the user view. *)
Definition two_gets : seqtype := [::out_get;out_get].

Lemma helper_trace_userview' : Trace (public_equiv _) \bot two_gets model_immediate_userview_concrete.
Proof.
  have <-: map_tr (@parse_output TPublicOutput TTypeSyscall) [::out_get';out_get'] = two_gets by [].
  eapply Trace_map. 2:eapply helper_trace'.
  mrw. ssa. subst. done.
Qed.

Lemma helper_trace_userview : Trace out_equiv_userviewC \bot two_gets model_immediate_userview_concrete.
Proof.
  eapply Trace_imp. 2:eapply helper_trace_userview'.
  intros. simpl in H. subst. auto.
Qed.

(* The same two public requests, seen through the public view. *)
Definition two_gets_public : seq ([T_in] + [Option TPublicOutput]) :=
  [:: inr (Some GetRequest); inr (Some GetRequest)].

Lemma helper_trace_publicview' : Trace (public_equiv _) \bot two_gets_public model_immediate_publicview_concrete.
Proof.
  have <-: map_tr (@public_output TPublicOutput TTypeSyscall) [::out_get';out_get'] = two_gets_public by [].
  eapply Trace_map. 2:eapply helper_trace'.
  mrw. ssa. subst. done.
Qed.

Lemma helper_trace_publicview : Trace (out_equiv_publicview TPublicOutput) \bot two_gets_public model_immediate_publicview_concrete.
Proof.
  eapply Trace_imp. 2:eapply helper_trace_publicview'.
  intros. simpl in H. subst. auto.
Qed.


(*Opaque otherwise the inversion tactic take forever*)
Opaque input_update output_update pool_input immediate_init no_output f_proj.

(* === Section 5: model_immediate_concrete is not non-interfering.  Witness: a short
   bot-trace of two public requests; insert a disk interrupt at the front
   (secret at bot); its pending flag reschedules the disk handler, which then
   runs its full two steps, so the expected second public output becomes None.
   Two public outputs suffice to refute NI.  (Paper, Section IV-A.) === *)
Lemma model_immediate_not_NI : ~ NI in_equiv out_equiv_concrete model_immediate_concrete.
Proof.
  intro. rewrite /NI in H. move: (H \bot). clear H.
  rewrite /NI_l. case=>_ [] + _. intros.
  move: helper_trace.
  move/a. move/(_ (inl tt) 0). simpl.
  have: dis in_equiv \bot (inl tt). ssa.
  move=>aa. move/(_ aa).
  move=>Htr. clear a aa.
  inv Htr; clear Htr; match_dd_out_first.
  do 2 (match goal with Ht : Trace _ _ (_ :: _) _ |- _ => inv Ht; clear Ht end;
        match_dd_out_first).
  (* the second public request is missing: the public slot emitted None *)
  match goal with Hr : rel _ _ _ _ |- _ => solve [move: Hr; clear; simpl; ssa] end.
Qed.

(* The leak survives the user view: the missing public request is a user-slot
   output, which [parse_output] keeps.  Same witness, same proof. *)
Lemma model_immediate_userview_not_NI : ~ NI in_equiv out_equiv_userviewC model_immediate_userview_concrete.
Proof.
  intro. rewrite /NI in H. move: (H \bot). clear H.
  rewrite /NI_l. case=>_ [] + _. intros.
  move: helper_trace_userview. rewrite /two_gets.
  move/a. move/(_ (inl tt) 0). simpl.
  have: dis in_equiv \bot (inl tt). ssa.
  move=>aa. move/(_ aa).
  move=>Htr. clear a aa.
  inv Htr; clear Htr; match_dd_out_first.
  do 2 (match goal with Ht : Trace _ _ (_ :: _) _ |- _ => inv Ht; clear Ht end;
        match_dd_out_first).
  match goal with Hr : rel _ _ _ _ |- _ => solve [move: Hr; clear; simpl; ssa] end.
Qed.

(* The leak needs only the public user's output: the missing public request is
   all the attacker sees, and it suffices.  Same witness, same proof. *)
Lemma model_immediate_publicview_not_NI :
  ~ NI in_equiv (out_equiv_publicview TPublicOutput) model_immediate_publicview_concrete.
Proof.
  intro. rewrite /NI in H. move: (H \bot). clear H.
  rewrite /NI_l. case=>_ [] + _. intros.
  move: helper_trace_publicview. rewrite /two_gets_public.
  move/a. move/(_ (inl tt) 0). simpl.
  have: dis in_equiv \bot (inl tt). ssa.
  move=>aa. move/(_ aa).
  move=>Htr. clear a aa.
  inv Htr; clear Htr; match_dd_out_first.
  do 2 (match goal with Ht : Trace _ _ (_ :: _) _ |- _ => inv Ht; clear Ht end;
        match_dd_out_first).
  match goal with Hr : rel _ _ _ _ |- _ => solve [move: Hr; clear; simpl; ssa] end.
Qed.

Transparent pool_input immediate_init no_output f_proj.


(*The rest of the file shows nonintereference of model2 and model3*)

(* Everything below is parametric in the model's four numeric/type parameters:
   the two user-slot alphabets (no part of the mechanism inspects a user-slot
   value) and the handler length / slice size (no stage of the state transition
   inspects the counter's value -- see the fv_NI stages in section 7c, which
   establish that the counter is public and then case on it abstractly).  The
   concrete corollaries are at the bottom of the file. *)
Section Parameters.

Variable Opub Opriv : Ty.       (*alphabets of the public and secret user slots*)
Variable runtime runs : nat.    (*handler length; handler runs per time slice*)

Lemma eqsum_llrr  (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B])  l i i' : rel (eqsum ARel BRel) l i i' -> is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'.
Proof.
  intros. destruct i. destruct i'. ssa.
  exfalso. ssa. destruct i'. ssa. ssa.
Qed.

Lemma eqsum_L_llrr (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l i i' : rel (eqsum_L ARel BRel) l i i' -> is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'.
Proof.
  intros. destruct i. destruct i'. ssa.
  exfalso. ssa. destruct i'. ssa. ssa.
Qed.

Lemma eqsum_split (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l i0 i1 : rel (eqsum ARel BRel) l i0 i1 -> (exists i0' i1', (i0 = inl i0' /\ i1 = inl i1' /\ rel ARel l i0' i1')) \/
                                                                                                              exists i0' i1', (i0 = inr i0' /\ i1 = inr i1' /\ rel BRel l i0' i1').
Proof.
  intros. apply eqsum_llrr in H as H'. destruct H'.
  destruct H0. destruct i0. destruct i1.
  left. exists i. exists i0. ssa.
  ssa. ssa. destruct i0. ssa.
  destruct i1. ssa.
  right. exists i. exists i0. ssa.
Qed.

Lemma eqsum_L_split (A B : Ty) (ARel : cEquiv [A]) (BRel : cEquiv [B]) l i0 i1 : rel (eqsum_L ARel BRel) l i0 i1 -> (exists i0' i1', (i0 = inl i0' /\ i1 = inl i1' /\ rel ARel l i0' i1')) \/
                                                                                                              exists i0' i1', (i0 = inr i0' /\ i1 = inr i1' /\ rel BRel l i0' i1').
Proof.
  intros. apply eqsum_L_llrr in H as H'. destruct H'.
  destruct H0. destruct i0. destruct i1.
  left. exists i. exists i0. ssa.
  ssa. ssa. destruct i0. ssa.
  destruct i1. ssa.
  right. exists i. exists i0. ssa.
Qed.

Lemma private_not_bot : forall (A : Ty) l (x y : [A]), l <> \bot -> x = y -> rel (private_equiv _) l x y.
Proof.
ssa.
Qed.

Lemma private_not_bot' : forall (A : Ty) l (x y : [A]), l <> \bot -> rel (private_equiv _) l x y -> x = y.
Proof.
ssa. de H0.
Qed.

Lemma eqmaybe_nonbot_not_bot' : forall (A : Ty) l (x y : [Option A]), l <> \bot -> rel (eqmaybe_all (private_equiv _)) l x y -> x = y.
Proof.
ssa. de x. de y. de H0. subst. done. de y.
Qed.

Lemma eqmaybe_all_not_bot : forall (A : Ty) l (x y : [Option A]), l <> \bot -> rel (eqmaybe_all (public_equiv _)) l x y -> x = y.
Proof.
ssa. de x. de y. subst. done. de y.
Qed.

Lemma eqmaybe_nonbot_not_bot : forall (A : Ty) l (x y : [Option A]), l <> \bot -> rel (eqmaybe_nonbot (private_equiv _)) l x y -> x = y.
Proof.
ssa. de x. de y. de H0. subst. done. de y.
Qed.

Lemma eqmaybe_nonbot_at_bot : forall (A : Ty) (x y : [Option A]), rel (eqmaybe_nonbot (private_equiv _)) \bot x y.
Proof.
  ssa. de x. de y. de y.
Qed.

Lemma private_bot : forall (A : Ty) (x y : [A]), rel ((private_equiv _)) \bot x y.
Proof.
  ssa.
Qed.

Hint Resolve private_bot.

Lemma public_equiv_eq : forall (A : Ty) l x y, rel (public_equiv A) l x y -> x = y.
Proof. ssa. Qed.

Lemma out_equiv_not_bot : forall i i' l, l <> \bot -> rel (out_equiv Opub Opriv) l i i' -> i = i'.
Proof.
  intros.
  move:H0. move/rel_eqpair=> [] + /rel_eqpair [] + /rel_eqpair [] + /rel_eqpair [] + /rel_eqpair [].
  move: i=>[a [b [c [d [e f]]]]].
  move: i'=>[a' [b' [c' [d' [e' f']]]]].  
  rewrite !pair_rewr.
  move=>/eqmaybe_all_not_bot=>->//.
  move=>/eqmaybe_nonbot_not_bot'=>->//.
  move=>/eqmaybe_all_not_bot=>->//.
  move/rel_eqmaybe_nonbot.
  case.
  move=>[x0][y0][]->[]-> /private_not_bot' ->//.
  move=>/eqmaybe_nonbot_not_bot=>->//.
  move=>/eqmaybe_all_not_bot=>->//.
  case. ssa.
  case. ssa.
  move=>[]->->.
  move=>/eqmaybe_nonbot_not_bot=>->//.
  move=>/eqmaybe_all_not_bot=>->//.  
Qed.



Lemma false_equiv_aware : forall l, aware false_equiv true l.
Proof.
intros. rewrite /aware. intros. ssa. subst. simpl. intro. ssa.
Qed.
(* false_equiv is private + public, like in_equiv: read a gate bit as a sum,
   false on the inl side (unobservable at bot) and true on the inr side
   (public).  It agrees with eqsum_L along bool_to_sum, on relatedness and on
   unobservability, at every level.  (Paper, Fig. 10.) *)
Definition bool_to_sum (b : bool) : [Sum Unit Unit] := if b then inr tt else inl tt.

Lemma false_equiv_sum_rel l b b' :
  rel false_equiv l b b' <->
  rel (eqsum_L (private_equiv Unit) (public_equiv Unit)) l (bool_to_sum b) (bool_to_sum b').
Proof.
rewrite /false_equiv /bool_to_sum /=.
case: b; case: b' => /=.
- by split=> _.
- by split.
- by split.
- split=> _ //.
  by case: (eqVneq l \bot) => [->|/eqP ?]; [right | left].
Qed.

Lemma false_equiv_sum_dis l b :
  dis false_equiv l b <->
  dis (eqsum_L (private_equiv Unit) (public_equiv Unit)) l (bool_to_sum b).
Proof.
rewrite /false_equiv /bool_to_sum /=; case: b => /=.
- by split; case.
- by split; [case | move=> ->].
Qed.


(* === Section 7a: the state equivalence.  Classification across two bot-related
   states: masks PUBLIC everywhere; the secret handlers' (disk, NOP)
   pending bits secret via private_pending_equiv; cur_pid's inl/inr tag PUBLIC but the
   bool inside inl (which handler) secret;
   re_sched, slice_count (the slice), scheduler/user pid all public.
   (Paper, Section V-A.) === *)
Definition pids_equiv : cEquiv [pids] := eqpair (eqsum (private_equiv _) (public_equiv _)) (public_equiv _).
Definition private_pending_equiv : cEquiv [ir_bits] := eqpair (private_equiv _) (public_equiv _).
Definition public_bits_equiv : cEquiv [ir_bits] := eqpair (public_equiv _) (public_equiv _).
Definition ic_equiv : cEquiv [ic] := eqpair private_pending_equiv (eqpair private_pending_equiv public_bits_equiv).
Definition bool_state_equiv : cEquiv [bool_state] := eqpair (public_equiv _) (eqpair (public_equiv _) ic_equiv).
Definition state_type_equiv : cEquiv [state_type] := eqpair pids_equiv bool_state_equiv.


Lemma state_type_equiv_not_bot : forall i i' l, l <> \bot -> rel state_type_equiv l i i' -> i = i'.
Proof.
  intros.
  move:H0.
  move/rel_eqpair=> [] /rel_eqpair[] + + /rel_eqpair [] + /rel_eqpair [] + /rel_eqpair [] /rel_eqpair [] + + /rel_eqpair[] /rel_eqpair[] + + /rel_eqpair [] + +.
  move: i=>[[a0 a1]] [b [b0 [[b1 b2 [[b3 b4 [b5 b6]]]]]]].
  move: i'=>[[a0' a1']] [b' [b0' [[b1' b2' [[b3' b4' [b5' b6']]]]]]].  
  rewrite !pair_rewr. 
  move=> /eqsum_split Hsplit.
  move=>/public_equiv_eq -> /public_equiv_eq -> /public_equiv_eq -> // /private_not_bot' -> // /public_equiv_eq -> // /private_not_bot' -> // /public_equiv_eq -> // /public_equiv_eq -> /public_equiv_eq ->.
  case: Hsplit.
  move=>[x][y][]->[]->/private_not_bot' ->//.
  move=>[x][y][]->[]-> /public_equiv_eq ->//.  
Qed.


Transparent input_update output_update pool_input immediate_init no_output f_proj.

Lemma in_equiv_eq i i0 l : rel in_equiv l i i0 -> i = i0.
Proof.
  destruct i as [[]|[]], i0 as [[]|[]]; simpl; intuition.
Qed.

(* === The composition-breakdown technique.  output_update is
     fun o => initiate_next o \o (advance_policy \o observe_policy o),
   and fv_NI_comp discharges fv_NI of a pipeline from fv_NI of its stages.  The
   input event equivalence is eqsum_L: an input may be unobservable, an output
   never is, which is why input_update_EP reduces to a condition on set_pending
   alone.  initiate_next is non-interfering only on states the sliced policy
   reaches, so for the sliced model output_update is proved under the slice
   invariant (sta_NI_pred in theorems.v). === *)
Lemma fv_NI_comp : forall (I V: Ty) (IRel : cEquiv [I]) (VRel : cEquiv [V]) (f f' : [I]  -> [V] ->  [V]),
    fv_NI IRel VRel VRel f -> fv_NI IRel VRel VRel f' -> fv_NI IRel VRel VRel (fun i => (f' i) \o (f i)).
Proof.
intros. move: H H0. rewrite /fv_NI. ssa.
Qed.

Definition ready_aux (v : [state_type]) := ir_ready v timer_irq /\ first_ready v = Some timer_irq \/ ~ ir_ready v timer_irq /\ ir_ready v disk_irq /\ first_ready v = Some disk_irq \/  ~ ir_ready v timer_irq /\ ~ ir_ready v disk_irq /\ ir_ready v nop_irq /\ first_ready v = Some nop_irq \/ ~ ir_ready v timer_irq /\ ~ ir_ready v disk_irq /\ ~ ir_ready v nop_irq /\ first_ready v = None.

Lemma ready_auxP v : ready_aux v.
Proof.
  rewrite /ready_aux.
  destruct (ir_ready v timer_irq) eqn:Heqn. left. ssa.
  rewrite /first_ready. rewrite /all_interrupts /ohead. rewrite /filter.
  rewrite Heqn. done.
  right.
  destruct (ir_ready v disk_irq) eqn:Heqn'.
  left. con. done. con. done.
  rewrite /first_ready /ohead /filter /all_interrupts Heqn Heqn' //.
  right.
  destruct (ir_ready v nop_irq) eqn:Heqn''.
  left. con. done. con. done. con. done.
  rewrite /first_ready /ohead /filter /all_interrupts Heqn Heqn' Heqn''//.
  rewrite /first_ready /ohead /filter /all_interrupts Heqn Heqn' Heqn''//. ssa.
Qed.


Definition ready_cases (v v' : [state_type]) := ready_aux v /\ ready_aux v'.

Definition ready_aux2 (v : [state_type]) := ir_ready v disk_irq /\ first_ready v = Some disk_irq \/
                                             ~ ir_ready v disk_irq /\ ir_ready v nop_irq /\ first_ready v = Some nop_irq \/
                                             ~ ir_ready v disk_irq /\ ~ ir_ready v nop_irq /\ first_ready v = None.

Definition ready_cases2 (v v' : [state_type]) := ir_ready v timer_irq /\ ir_ready v' timer_irq /\ first_ready v = Some timer_irq /\ first_ready v' = Some timer_irq \/
                                                  ~ ir_ready v timer_irq /\ ~ ir_ready v' timer_irq /\
                                                    ready_aux2 v /\ ready_aux2 v'.

Lemma ready_casesP v v' : ready_cases v v'.
Proof.
  rewrite /ready_cases. con. apply ready_auxP. apply ready_auxP.
Qed.

Lemma ready_cases2P v v' : ir_ready v timer_irq = ir_ready v' timer_irq -> ready_cases2 v v'.
Proof.
  rewrite /ready_cases2.
  move: (ready_casesP v v'). rewrite /ready_cases. case.
  rewrite /ready_aux. intros. rewrite H in a b. rewrite H.
  de a. de b.
  de H2. de H2. de H0. de b. de H3. right. ssa. rewrite /ready_aux2. ssa. rewrite /ready_aux2. ssa.
  de H3. right. ssa.
  rewrite /ready_aux2;ssa.
  rewrite /ready_aux2;ssa.
  right. ssa.
  rewrite /ready_aux2;ssa.
  rewrite /ready_aux2;ssa.
  de H0.
  de b. de H4.
  right. ssa.
  rewrite /ready_aux2;ssa.
  rewrite /ready_aux2;ssa.
  de H4.
  right.
  ssa.
  rewrite /ready_aux2;ssa.
  rewrite /ready_aux2;ssa.
  right.
  ssa; rewrite /ready_aux2;ssa.
  de b. de H4.
  right;  rewrite /ready_aux2;ssa.
  de H4.
  right;  rewrite /ready_aux2;ssa.
  right;  rewrite /ready_aux2;ssa.
Qed.

Lemma first_ready_update_re_sched : forall v b, first_ready (update_re_sched v b) = first_ready v.
Proof.
  intros. cbv. ssa.
Qed.

(* === Leaf obligations for the three replaceable slots ===

   The pool's userspace and scheduler slots are discharged by these three
   facts and nothing else.  Stating them separately makes explicit what the
   assembled proof needs of each slot: an NI process at the classification
   its slot declares.  (Paper, Section V-D.) *)

(* Slot 5, the public user process.  Its output slot is public, so it may
   emit anything as long as it emits it unconditionally. *)
Lemma p_pub_concrete_NI : NI (public_equiv Empty) (public_equiv TPublicOutput) p_pub_concrete.
Proof.
  apply out_NI.
Qed.

(* Slot 4, the secret user process.  Both its input (the disk handler's
   [Notify]) and its output are secret. *)
Lemma p_priv_concrete_NI : NI (private_equiv THandlerOutput) (private_equiv TTypeSyscall) p_priv_concrete.
Proof.
  eapply map_NI.
  mrw. intros. apply rel_eqsum_L. eauto.
  mrw. intros. apply dis_eqsum_L. done.
  mrw. intros. move: H.
  instantiate (1:= eqsum_L _ _). intros.
  destruct i. destruct i'. apply rel_refl. ssa.
  destruct i'. ssa.
  apply rel_eqsum_L2' in H.
  destruct i. destruct i0.
  2: apply loop_NI.
  destruct i1. destruct i2.
  move:H. instantiate (1:=  (eqpair (private_equiv Bool) _)).
  move/rel_eqpair. case. rewrite !pair_rewr.
  intros. clear b. ssa. destruct a. ssa. subst. case_if. subst. ssa. subst. ssa.
  ssa.

  
  eapply map_NI.
  apply f_NI_id.
  apply f_PU_id.

  mrw. intros. apply rel_eqsum_L2. eauto.

  apply sta_NI.
  mrw. intros. eauto.
  mrw. intros.
  destruct i. destruct i'. apply rel_eqsum_L' in H.
  ssa. de H. de H0. subst. left. ssa.
  ssa. destruct i'. ssa. apply rel_refl.
  mrw. intros. destruct i. apply dis_eqsum_L2 in H. ssa. ssa.
  apply out_NI.
  Unshelve. all: exact (public_equiv _).
Qed.

(* Slot 3, the scheduler.  Its output -- the pid it picks -- is public. *)
Lemma scheduler_NI : NI (public_equiv Empty) (public_equiv Nat) scheduler.
Proof.
  eapply map_NI. eauto. eauto.
  instantiate (1:=eqpair _ _).
  mrw. move=> l i i' /rel_eqpair[] + _.
  instantiate (1:= public_equiv _). move=>/public_equiv_eq ->. ssa.
  eapply sta_NI.
  mrw. intros. move: H0.
  move/public_equiv_eq=>->//.
  mrw. intros. eauto.
  mrw. intros. auto.
  apply out_NI.
  Unshelve. all: exact (public_equiv _).
Qed.



(* === Section 6: model_sliced is non-interfering.  Assembled from the generic
   composition theorems (par_NI, sta_NI, swi_NI, map/output-weakening) applied
   to the pool; the only non-mechanical obligation is fv_NI of the state
   transition (section 7).  (Paper, Section V.)

   The result holds for *any* scheduler and any two user processes that are
   themselves non-interfering at the classification their slot declares.  That
   it can: [state_step] never reads a user process's output value, only whether
   the slot produced one -- [is_sched_out] matches [(None,(None,(Some n,_)))] --
   so no user behaviour reaches the schedule, and fv_NI, the one hard
   obligation, does not depend on which processes fill the slots.

   [p_pub_concrete_NI], [p_priv_concrete_NI] and [scheduler_NI] above are the instances that give
   back the concrete system; see the corollaries at the end of the file. === *)

(* The parametric proof cannot unfold its own processes, so [rewr] drops
   /p_pub_concrete /alternate /p_priv_concrete /scheduler. *)
Ltac rewr ::= rewrite /model_sliced /model /reactive_system /pool /process_pool /slot_initial /slot_procs /pool_input /tI_o /ir_handler /f_proj /low_out.

Section Parametric.

Variable p_pub : Proc Empty Opub.
Variable p_priv : Proc THandlerOutput Opriv.
Variable p_sched : Proc Empty Nat.

Hypothesis p_pub_NI : NI (public_equiv Empty) (public_equiv Opub) p_pub.
Hypothesis p_priv_NI : NI (private_equiv THandlerOutput) (private_equiv Opriv) p_priv.
Hypothesis p_sched_NI : NI (public_equiv Empty) (public_equiv Nat) p_sched.

(* The slice stages write two fields the same way in both related states: the
   NOP pending bit (private) at each handler boundary, and re_sched (public) when
   the slice opens.  Writing a field identically preserves the relation. *)
Lemma update_pending_rel : forall l v v' ir b,
  rel state_type_equiv l v v' ->
  rel state_type_equiv l (update_ir_pending v ir b) (update_ir_pending v' ir b).
Proof.
  intros l v v' ir b.
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[]H2 /rel_eqpair[]/rel_eqpair[]H3 H4/rel_eqpair[]/rel_eqpair[]H5 H6/rel_eqpair[]H7 H8.
  move: H0 H1 H2 H3 H4 H5 H6 H7 H8.
  move: v=> [[cur prev]] [re_sched] [slice_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sched'] [slice_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].
  rewrite /get_ic /update_ic /get_bool_state /update_bool_state /get_ir_mask /get_mask' /update_ir_pending /update_ir_bits /update_ir_bits' !pair_rewr.
  move=> H0 H1 H2 H3 H4 H5 H6 H7 H8.
  rewrite /get_ic /update_ic /get_bool_state /update_bool_state /get_ir_mask /get_mask' /update_ir_pending /update_ir_bits /update_ir_bits' !pair_rewr.
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2.
  rewrite !pair_rewr.
  con. done.
  case: ir => [[]|]; rewrite /get_ir_bits /get_ir_bits' /get_ic /get_bool_state !pair_rewr;
  repeat (apply/rel_eqpair2; con); rewrite ?pair_rewr; try done; try apply rel_eq; eauto.
Qed.

Lemma update_re_sched_rel : forall l v v' b,
  rel state_type_equiv l v v' ->
  rel state_type_equiv l (update_re_sched v b) (update_re_sched v' b).
Proof.
  intros l v v' b.
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[]H2 H3.
  move: H0 H1 H2 H3.
  move: v=> [[cur prev]] [re_sched] [slice_count] ic.
  move: v'=> [[cur' prev']] [re_sched'] [slice_count'] ic'.
  rewrite /update_re_sched /get_bool_state /update_bool_state !pair_rewr.
  move=> H0 H1 H2 H3.
  apply/rel_eqpair2; con; rewrite !pair_rewr; first done.
  apply/rel_eqpair2; con; rewrite !pair_rewr; first by apply rel_eq.
  apply/rel_eqpair2; con; rewrite !pair_rewr; done.
Qed.

(* The scheduler's choice: it reads only the scheduler's output, which is
   public, and whether the user slots emitted. *)
Lemma apply_scheduler_choice_NI :
  fv_NI (out_equiv Opub Opriv) state_type_equiv state_type_equiv (@apply_scheduler_choice Opub Opriv).
Proof.
  rewrite /apply_scheduler_choice.

  mrw. intros.

  destruct (eqVneq l \bot).
  2: {  apply out_equiv_not_bot in H. 2:apply/eqP=>//. subst.
        apply state_type_equiv_not_bot in H0. 2:apply/eqP=>//. subst. eauto. }
  subst.

  move: v H0=> [[cur prev]] [re_sched] [slice_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sched'] [slice_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] /public_equiv_eq H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H=> /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] _ /rel_eqpair[] _ +.
  move: i=>[a[] b[] c[] d[] e f].
  move: i'=>[a'[] b'[] c'[] d'[] e' f'].
  rewrite !pair_rewr /is_sched_out. subst.

  case/rel_eqmaybe_all2.
  move=>[]x []y []-> []->// /public_equiv_eq ->//.
  move=>[]->[]->//.

  case/rel_eqmaybe_all2.
  move=>[]x' []y' []-> []->// Hpr.
  move=>[]->[]->//.

  case/rel_eqmaybe_all2.
  move=>[]x0 []y0 []-> []->// /public_equiv_eq ->//.

  move=>_. (*drop*)

  apply/rel_eqpair2;con;try solve [ssa].

  move=>[]->[]->//.
Qed.

Lemma update_slice_count_rel : forall l v v' c,
  rel state_type_equiv l v v' ->
  rel state_type_equiv l (update_slice_count v c) (update_slice_count v' c).
Proof.
  intros l v v' c.
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[]H2 H3.
  move: H0 H1 H2 H3.
  move: v=> [[cur prev]] [re_sched] [slice_count] ic.
  move: v'=> [[cur' prev']] [re_sched'] [slice_count'] ic'.
  rewrite /update_slice_count /update_ic_count /get_ic_count /get_bool_state /update_bool_state ?pair_rewr.
  move=> H0 H1 H2 H3.
  apply/rel_eqpair2; con; rewrite ?pair_rewr; first done.
  apply/rel_eqpair2; con; rewrite ?pair_rewr; first done.
  apply/rel_eqpair2; con; rewrite ?pair_rewr; [by apply rel_eq | done].
Qed.

Lemma update_mask_rel : forall l v v' ir b,
  rel state_type_equiv l v v' ->
  rel state_type_equiv l (update_ir_mask v ir b) (update_ir_mask v' ir b).
Proof.
  intros l v v' ir b.
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[]H2 /rel_eqpair[]/rel_eqpair[]H3 H4/rel_eqpair[]/rel_eqpair[]H5 H6/rel_eqpair[]H7 H8.
  move: H0 H1 H2 H3 H4 H5 H6 H7 H8.
  move: v=> [[cur prev]] [re_sched] [slice_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sched'] [slice_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].
  rewrite /get_ic /update_ic /get_bool_state /update_bool_state /get_ir_mask /get_mask' /update_ir_mask /update_ir_bits /update_ir_bits' !pair_rewr.
  move=> H0 H1 H2 H3 H4 H5 H6 H7 H8.
  rewrite /get_ic /update_ic /get_bool_state /update_bool_state /get_ir_mask /get_mask' /update_ir_mask /update_ir_bits /update_ir_bits' !pair_rewr.
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2.
  rewrite !pair_rewr.
  con. done.
  case: ir => [[]|]; rewrite /get_ir_bits /get_ir_bits' /get_ic /get_bool_state ?pair_rewr;
  repeat (apply/rel_eqpair2; con); rewrite ?pair_rewr; try done; try apply rel_eq; eauto.
Qed.

(* The slice's mask operations write the same values into both states. *)
Lemma set_masks_rel l v v' :
  rel state_type_equiv l v v' -> rel state_type_equiv l (set_masks v) (set_masks v').
Proof.
  move=> H; cbv beta iota fix delta [set_masks all_interrupts foldr].
  by do 3 apply update_mask_rel.
Qed.

Lemma unset_masks_rel l v v' :
  rel state_type_equiv l v v' -> rel state_type_equiv l (unset_masks v) (unset_masks v').
Proof.
  move=> H; cbv beta iota fix delta [unset_masks all_interrupts foldr].
  by do 3 apply update_mask_rel.
Qed.

Lemma queue_secret_run_rel l v v' :
  rel state_type_equiv l v v' ->
  rel state_type_equiv l (queue_secret_run v) (queue_secret_run v').
Proof.
  move=> H; rewrite /queue_secret_run.
  apply update_pending_rel; apply update_mask_rel; exact: unset_masks_rel.
Qed.

Lemma close_slice_rel l v v' :
  rel state_type_equiv l v v' -> rel state_type_equiv l (close_slice v) (close_slice v').
Proof.
  move=> H; rewrite /close_slice.
  apply update_slice_count_rel; apply update_mask_rel; exact: set_masks_rel.
Qed.

(* === initiate_next, through the public part of the state ===

   At level \bot two states are related exactly when their public fields
   agree; [pub_view] collects them.  The scheduler and handler bookkeeping in
   [initiate_next] computes public fields from public fields, so it suffices to
   show that two related states take the same branch, up to which secret
   handler they start.  Whether a handler is running and whether the timer
   handler is ready are public.  Whether a secret handler is ready is not, and
   this is where the slice invariant enters: by [open_iff_ready] it
   agrees with whether a slice is open, which is public. *)
Definition pub_view (v : [state_type]) :=
  (if get_cur_pid v is inr n then Some n else None, get_prev_pid v, get_re_sched v,
   get_slice_count v, get_ir_mask v timer_irq, get_ir_mask v disk_irq,
   get_ir_mask v nop_irq, get_ir_pending v timer_irq).

Lemma state_rel_bot v v' : rel state_type_equiv \bot v v' <-> pub_view v = pub_view v'.
Proof.
move: v v' => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]] [[cur' prev'] [rs' [c' [[dp' dm'] [[kp' km'] [tp' tm']]]]]].
split.
- move/rel_eqpair=> [] /rel_eqpair[] + + /rel_eqpair [] + /rel_eqpair [] + /rel_eqpair [] /rel_eqpair [] + + /rel_eqpair[] /rel_eqpair[] + + /rel_eqpair [] + +.
  rewrite !pair_rewr => /eqsum_split Hs.
  move=> /public_equiv_eq -> /public_equiv_eq -> /public_equiv_eq -> _ /public_equiv_eq -> _ /public_equiv_eq -> /public_equiv_eq -> /public_equiv_eq ->.
  by case: Hs => [[x][y][->][->] _|[x][y][->][->] /public_equiv_eq ->].
- rewrite /pub_view /get_cur_pid /get_prev_pid /get_pids /get_re_sched /get_bool_state /get_slice_count /get_ic_count /get_ir_mask /get_mask' /get_ir_bits /get_ir_bits' /get_ic /get_ir_pending /get_pending' /=.
  case=> Hc -> -> -> -> -> -> ->.
  by case: cur cur' Hc => [b|n] [b'|n'] //= => [_|[->]]; intuition.
Qed.

(* Starting a handler: the public result depends only on whether it is the
   timer's. *)
Lemma pub_view_initiate_handler ir ir' w w' :
  pub_view w = pub_view w' -> (ir == timer_irq) = (ir' == timer_irq) ->
  pub_view (initiate_handler ir w) = pub_view (initiate_handler ir' w').
Proof.
move: w w' => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]] [[cur' prev'] [rs' [c' [[dp' dm'] [[kp' km'] [tp' tm']]]]]].
rewrite /pub_view /get_cur_pid /get_prev_pid /get_pids /get_re_sched /get_bool_state /get_slice_count /get_ic_count /get_ir_mask /get_mask' /get_ir_bits /get_ir_bits' /get_ic /get_ir_pending /get_pending' /=.
case=> Hc -> -> -> -> -> -> ->.
case: ir ir' => [[]|] [[]|] //= _; case: cur cur' Hc => [b|n] [b'|n'] //=; try case=> ->; try case: n' => [|n']; by vm_compute.
Qed.

(* The last branch of [initiate_next]: no handler ready. *)
Definition leave_handlers (w : [state_type]) :=
  if is_handler_pid w then if get_re_sched w then initiate_scheduler w else initiate_prev_pid w else w.

Lemma pub_view_leave_handlers w w' :
  pub_view w = pub_view w' -> pub_view (leave_handlers w) = pub_view (leave_handlers w').
Proof.
move: w w' => [[cur prev] [rs [c [[dp dm] [[kp km] [tp tm]]]]]] [[cur' prev'] [rs' [c' [[dp' dm'] [[kp' km'] [tp' tm']]]]]].
rewrite /pub_view /get_cur_pid /get_prev_pid /get_pids /get_re_sched /get_bool_state /get_slice_count /get_ic_count /get_ir_mask /get_mask' /get_ir_bits /get_ir_bits' /get_ic /get_ir_pending /get_pending' /=.
case=> Hc -> -> -> -> -> -> ->.
case: cur cur' Hc => [b|n] [b'|n'] //=; try case=> ->; try case: n' => [|n']; case: rs'; by vm_compute.
Qed.

Lemma first_readyE u : first_ready u =
  if ir_ready u timer_irq then Some timer_irq else
  if ir_ready u disk_irq then Some disk_irq else
  if ir_ready u nop_irq then Some nop_irq else None.
Proof.
rewrite /first_ready /=.
by case: (ir_ready u timer_irq); case: (ir_ready u disk_irq); case: (ir_ready u nop_irq).
Qed.

(* ⦃≐ ∧ open_iff_ready on both sides⦄ initiate_next ⦃≐⦄ *)
Lemma initiate_next_NI_on l (o o' : [T_out Opub Opriv]) v v' :
  rel (out_equiv Opub Opriv) l o o' -> rel state_type_equiv l v v' ->
  open_iff_ready v -> open_iff_ready v' ->
  rel state_type_equiv l (initiate_next o v) (initiate_next o' v').
Proof.
move=> Ho Hv Sv Sv'.
have Hs := apply_scheduler_choice_NI Ho Hv.
case: (apply_scheduler_choice_gated o v) => Mv _ _ Rv Ov.
case: (apply_scheduler_choice_gated o' v') => Mv' _ _ Rv' Ov'.
have {Sv Mv Rv Ov} Sw : open_iff_ready (apply_scheduler_choice o v)
  by rewrite /open_iff_ready Mv Rv Ov.
have {Sv' Mv' Rv' Ov'} Sw' : open_iff_ready (apply_scheduler_choice o' v')
  by rewrite /open_iff_ready Mv' Rv' Ov'.
rewrite /initiate_next; cbv zeta.
move: (apply_scheduler_choice o v) (apply_scheduler_choice o' v') Hs Sw Sw' => w w' Hw Sw Sw'.
clear Ho Hv.
case: (eqVneq l \bot) => [El|Hl]; last first.
  by rewrite (state_type_equiv_not_bot (elimN eqP Hl) Hw); apply rel_refl.
subst l.
move/state_rel_bot: Hw => Hw.
have := Hw; rewrite /pub_view => -[_ _ _ Hc Ht Hd Hn Hp].
(* a handler is running: nothing changes *)
rewrite !masks_setE Ht Hd Hn.
case Ms: [&& _, _ & _]; first by apply/state_rel_bot.
(* otherwise both states agree on whether a secret handler is ready *)
move: Sw Sw'; rewrite /open_iff_ready !masks_setE Ht Hd Hn Ms => Sw Sw'.
have Hsr : secret_ready w = secret_ready w' by rewrite -Sw // -Sw' // /slice_open Hc.
have Hrt : ir_ready w timer_irq = ir_ready w' timer_irq by rewrite /ir_ready Hp Ht.
apply/state_rel_bot.
move: Hsr; rewrite /secret_ready !first_readyE Hrt.
case: ifP => _; first by move=> _; apply: pub_view_initiate_handler.
case: (ir_ready w disk_irq); case: (ir_ready w nop_irq); case: (ir_ready w' disk_irq); case: (ir_ready w' nop_irq) => //= _;
  first [by apply: pub_view_initiate_handler | by apply: pub_view_leave_handlers].
Qed.

(* === The stages of the sliced state update === *)

(* set_pending: the input summand *)
Lemma set_pending_NI : fv_NI in_equiv state_type_equiv state_type_equiv set_pending.
Proof.

  rewrite /set_pending.
  mrw. intros.
  apply in_equiv_eq in H;subst.
  move: H0.
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[]H2 /rel_eqpair[]/rel_eqpair[]H3 H4/rel_eqpair[]/rel_eqpair[]H5 H6/rel_eqpair[]H7 H8.
  move: H0 H1 H2 H3 H4 H5 H6 H7 H8.
  move: v=> [[cur prev]] [re_sched] [slice_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sched'] [slice_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].
  rewrite /get_ic /update_ic /get_bool_state /update_bool_state /get_ir_mask /get_mask' /update_ir_pending /update_ir_bits /update_ir_bits' !pair_rewr.
  move=> H0 H1 H2 H3 H4 H5 H6 H7 H8.
  rewrite /get_ic /update_ic /get_bool_state /update_bool_state /get_ir_mask /get_mask' /update_ir_pending /update_ir_bits /update_ir_bits' !pair_rewr.    

  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2.
  rewrite !pair_rewr.
  con. done.
  apply/rel_eqpair2;con. 
  apply/rel_eqpair2;con.

  destruct i';rewrite !pair_rewr;eauto.
  destruct i';rewrite !pair_rewr;eauto.
  apply/rel_eqpair2;con.
  apply/rel_eqpair2;con.  
  destruct i';rewrite !pair_rewr //.
  destruct i';rewrite !pair_rewr //.
  destruct i';rewrite !pair_rewr //.    
Qed.

Lemma set_pending_EP : f_EP in_equiv state_type_equiv set_pending.
Proof.
  rewrite /set_pending.
  mrw. intros.
  case: i H => [[]|[]] H; simpl in H; last done. subst.

  move: v => [[cur prev]] [re_sched] [slice_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa. de cur.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa. ssa.
Qed.

(* service_policy: observe_timer_output, then tick_slice.  Both read only public
   fields, so they need no invariant. *)
Lemma observe_timer_output_NI :
  fv_NI (out_equiv Opub Opriv) state_type_equiv state_type_equiv (@observe_timer_output runtime runs Opub Opriv).
Proof.
  mrw. intros.
  rewrite /observe_timer_output.

  have: tI_out i = tI_out i'.

  move: v H0=> [[cur prev]] [re_sched] [slice_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sched'] [slice_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H=> /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ +.
  move: i=>[a[] b[] c[] d[] e f].
  move: i'=>[a'[] b'[] c'[] d'[] e' f']. 
  rewrite !pair_rewr /is_sched_out.  

  case/rel_eqmaybe_all2.
  move=>[]x'[]y'[]->[]->/public_equiv_eq->//.
  move=>[]->->//.

  move=>->.

  destruct ((tI_out i')). destruct h. done.
  apply update_re_sched_rel.
  apply/rel_eqpair2. con;ssa. done.
Qed.

Lemma sliced_service_NI :
  fv_NI (out_equiv Opub Opriv) state_type_equiv state_type_equiv (@sliced_service runtime runs Opub Opriv).
Proof.
  rewrite /sliced_service.
  apply fv_NI_comp; first exact: observe_timer_output_NI.

  (*tick_slice: reads only the counter, which is public, so both states take
    the same branch, and each branch writes the same values into both*)
  mrw. intros.
  rewrite /tick_slice.

  have: get_slice_count v = get_slice_count v'.

  move: v H0=> [[cur prev]] [re_sched] [slice_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sched'] [slice_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H2=>/public_equiv_eq->//.
  move=>->.

  case: (get_slice_count v') => [|[|n]].
  - done.
  - by apply close_slice_rel.
  - case: (slice_at_boundary _ _).
    + by apply queue_secret_run_rel; apply update_slice_count_rel.
    + by apply update_slice_count_rel.
Qed.

(* === Any interrupt policy that meets three obligations is non-interfering:
   its initial state satisfies the slice invariant, its service policy takes the
   invariant to the fact at the choice point, and its service policy is
   non-interfering on related states.  The rest of the proof does not depend on
   the policy. === *)
Section Policy.

Variable init_policy : [state_type].
Variable observe_policy : [T_out Opub Opriv] -> [state_type] -> [state_type].
Variable advance_policy : [state_type] -> [state_type].

Hypothesis init_inv : secret_gated init_policy.
Hypothesis service_gated : forall o v, secret_gated v ->
  secret_gated_at_boundary (advance_policy (observe_policy o v)).
Hypothesis service_NI : fv_NI (out_equiv Opub Opriv) state_type_equiv state_type_equiv
  (fun o => advance_policy \o observe_policy o).

(* The output summand, on states satisfying the slice invariant: the service
   policy keeps states related (service_NI) and establishes the fact at the
   choice point (service_gated), which gives initiate_next what it needs
   (secret_gated_at_boundary_ready). *)
Lemma policy_output_NI_on :
  fv_NI_on secret_gated (out_equiv Opub Opriv) state_type_equiv
    (output_update observe_policy advance_policy).
Proof.
move=> l o o' Ho v v' Pv Pv' Hv /=.
apply: initiate_next_NI_on; first exact: Ho.
- exact: (service_NI Ho Hv).
- exact/secret_gated_at_boundary_ready/service_gated.
- exact/secret_gated_at_boundary_ready/service_gated.
Qed.

(* The input update.  An event equivalence never relates an inl to an inr, and an
   output fed back leaves the state alone. *)
Lemma input_update_NI :
  fv_NI (eqsum_L in_equiv (out_equiv Opub Opriv)) state_type_equiv state_type_equiv
    (@input_update Opub Opriv).
Proof.
move=> l e e' He v v' Hv.
case: e e' He => [i|o] [i'|o'] He /=.
- apply: set_pending_NI Hv; exact: rel_eqsum_L' He.
- by case/eqsum_L_llrr: He => -[].
- by case/eqsum_L_llrr: He => -[].
- exact: Hv.
Qed.

(* Under eqsum_L only an inl is ever unobservable. *)
Lemma input_update_EP :
  f_EP (eqsum_L in_equiv (out_equiv Opub Opriv)) state_type_equiv (@input_update Opub Opriv).
Proof. by move=> l [i|o] Hi v //; apply: set_pending_EP. Qed.

(* The state cell: the first hard step of the proof of model_policy_NI.  For any
   inner process, the obligations of sta_NI_pred hold with the slice invariant.
   (Paper, Section V-C.) *)
Lemma policy_state_cell_NI p :
  NI (eqpair_R state_type_equiv (eqsum_L in_equiv (out_equiv Opub Opriv)))
     (out_equiv Opub Opriv) p ->
  NI (eqsum_L in_equiv (out_equiv Opub Opriv))
     (eqpair state_type_equiv (out_equiv Opub Opriv))
     (sta (@input_update Opub Opriv)
        (output_update observe_policy advance_policy) init_policy p).
Proof.
move=> Hp.
apply: (@sta_NI_pred _ _ _ secret_gated) Hp.
- move=> e v; exact: input_update_gated.
- move=> o v Hv; exact/initiate_next_gated/service_gated.
- exact: policy_output_NI_on.
- move=> l e e' He v v' _ _ Hv; exact: (input_update_NI He Hv).
- move=> l e He v _; exact: (input_update_EP He).
- exact: init_inv.
Qed.

(* One slot of the pool, as process_pool builds it.  [proj] is the slot's part of
   the fed-back handler output. *)
Definition pool_slot (A O : Ty) (n : nat) (b : bool)
    (proj : [T_intermediate] -> [Option A]) (p : Proc A O) :
    Proc (Times cur_pid T_intermediate) (Option O) :=
  map ((fun i => (slot_pid i.1 == n, proj i.2))
         : [Times cur_pid T_intermediate] -> [Times Bool (Option A)]) id
    (swi b (maybe (map id ((fun o => (true, o)) : [O] -> [Times Bool O]) p))).

(* The equivalence on what reaches a slot: the current pid and the handler output. *)
Definition slot_in_equiv : cEquiv [Times cur_pid T_intermediate] :=
  eqpair (eqsum (private_equiv Bool) (public_equiv _)) (eqmaybe_nobody (private_equiv _)).

(* The second hard step, for a slot no secret pid selects.  Both secret pids close
   its gate, so the gate is public and every level is aware of it: the attacker
   sees whether the slot ran.  (Paper, Section V-D.) *)
Lemma slot_visible_NI (A O : Ty) n b proj (IRel : cEquiv [A]) (YRel : cEquiv [O]) p :
  slot_pid (inl true) != n -> slot_pid (inl false) != n ->
  f_NI (eqmaybe_nobody (private_equiv _)) (eqmaybe_nobody IRel) proj ->
  NI IRel YRel p ->
  NI slot_in_equiv (eqmaybe_all YRel) (pool_slot n b proj p).
Proof.
move=> Ht Hf Hproj Hp.
rewrite /pool_slot /slot_in_equiv.
eapply map_NI.
instantiate (1:= eqpair_LR false_equiv (eqmaybe_nobody IRel)).
- mrw. move=> l i i' /rel_eqpair[Hpid Hin].
  apply rel_eqpair_LR2. split; last exact: Hproj.
  case/eqsum_split: Hpid.
  + have N z : (slot_pid (inl z) == n) = false by case: z; apply/negbTE.
    move=> [x][y][Ei [Ei' _]]; rewrite Ei Ei'.
    by move: (N x) (N y); rewrite /= => -> ->.
  + by move=> [x][y][-> [-> /public_equiv_eq ->]].
- mrw. by move=> l i.
- instantiate (1:= eqmaybe_aware YRel false_equiv).
  mrw. move=> l [x|] [y|] H.
  + exact: H.
  + by case: H=> _ /(_ (@false_equiv_aware l)).
  + by case: H=> /(_ (@false_equiv_aware l)).
  + done.
- apply swi_NI.
  + move=> l. left. exact: false_equiv_aware.
  + eapply maybe_NI. eapply map_NI; eauto.
    mrw. intros. apply rel_eqpair_LR2. con. auto. eauto.
Qed.

(* The second hard step, for a slot a secret pid selects.  Which secret pid is
   current is private, so the gate is private and the attacker cannot trust it;
   instead it sees none of the slot's outputs.  (Paper, Section V-D.) *)
Lemma slot_hidden_NI (A O : Ty) n b proj (IRel : cEquiv [A]) (YRel : cEquiv [O]) p :
  f_NI (eqmaybe_nobody (private_equiv _)) (eqmaybe_nobody IRel) proj ->
  NI IRel (private_equiv O) p ->
  NI slot_in_equiv (eqmaybe_nonbot (private_equiv O)) (pool_slot n b proj p).
Proof.
move=> Hproj Hp.
rewrite /pool_slot /slot_in_equiv.
eapply map_NI.
instantiate (1:= eqpair_LR (private_equiv _) (eqmaybe_nobody IRel)).
- mrw. move=> l i i' /rel_eqpair[Hpid Hin].
  apply rel_eqpair_LR2. split; last exact: Hproj.
  case: (eqVneq l \bot) => [->|/eqP Hl]; first exact: private_bot.
  refine (private_not_bot Hl _).
  case/eqsum_split: Hpid.
  + move=> [x][y][Ei [Ei' Hxy]]; rewrite Ei Ei'.
    by rewrite (private_not_bot' Hl Hxy).
  + by move=> [x][y][-> [-> /public_equiv_eq ->]].
- mrw. by move=> l i.
- instantiate (1:= eqmaybe_aware (private_equiv _) (private_equiv _)).
  mrw. intros. apply rel_eqmaybe_aware2 in H.
  destruct H. destruct H. destruct H. destruct H. destruct H0.
  subst. apply rel_eqmaybe_all. eauto.
  destruct H. destruct H. subst. auto.
  destruct H. destruct i. ssa. destruct i'. ssa. ssa. de i'.
- apply swi_NI.
  + move=> l.
    destruct (eqVneq l \bot). subst. right.
    (* At bot the gate cannot be trusted, but everything the switch emits is
       unobservable there: the gate is hidden, so None is, and so is every
       payload. *)
    apply oblivious_all_dis. case=> [o|] /=; first done.
    move=>Ha. have Hr : rel (private_equiv Bool) \bot true false by (simpl; right).
    by move: (Ha _ Hr)=>[].
    left. intro. intros.
    move/private_not_bot' : H=>->//. ssa.
    intro. subst. rewrite eqxx in i. done.
    intro. subst. rewrite eqxx in i. done.
  + apply maybe_NI. eapply map_NI; eauto.
    mrw. intros. apply rel_eqpair_LR2. con. auto. eauto.
Qed.

(* The handlers: a counter, at the equivalence of its output. *)
Lemma ir_handler_private_NI :
  NI (public_equiv Empty) (private_equiv THandlerOutput) (ir_handler runtime).
Proof.
  rewrite /ir_handler.
  eapply map_NI. eauto. eauto.
  mrw. intros.
  move:H. instantiate (1:=eqpair (private_equiv _) (public_equiv _)).
  move/rel_eqpair. case=>HH _.
  simpl in HH. destruct HH. destruct H. rewrite H0.
  case_if. auto. auto. subst. auto.
  eapply sta_NI.
  mrw. intros. simpl in H0. destruct H0. ssa. subst. auto.
  mrw. intros. auto.
  mrw. intros. auto.
  apply out_NI.
  Unshelve. all: apply public_equiv.
Qed.

Lemma ir_handler_public_NI :
  NI (public_equiv Empty) (public_equiv THandlerOutput) (ir_handler runtime).
Proof.
  rewrite /ir_handler.
  eapply map_NI. eauto. eauto.
  instantiate (1:=eqpair _ _).
  mrw. move=> l i i' /rel_eqpair[] + _.
  instantiate (1:= public_equiv _). move=>/public_equiv_eq ->. ssa.
  eapply sta_NI.
  mrw. intros. move: H0.
  move/public_equiv_eq=>->//.
  mrw. intros. eauto.
  mrw. intros. auto.
  apply out_NI.
  Unshelve. all: apply public_equiv.
Qed.

Lemma slot_no_input (A : Ty) (IRel : cEquiv [A]) :
  f_NI (eqmaybe_nobody (private_equiv THandlerOutput)) (eqmaybe_nobody IRel)
       (fun _ => None).
Proof. by mrw. Qed.

Theorem model_policy_NI : NI in_equiv (out_equiv Opub Opriv)
  (model runtime init_policy observe_policy advance_policy p_pub p_priv p_sched).
Proof.
  rewr;simpl;rewr;simpl.
  eapply map_NI.
  instantiate (1:= eqsum_L in_equiv (out_equiv Opub Opriv)). ssa. ssa.
  mrw. intros.
  2:eapply loop_NI. apply eqsum_L_llrr in H as H'. destruct H'.
  destruct i. destruct i'. ssa. ssa. ssa.
  destruct i. ssa. destruct i'. ssa.
  apply rel_eqsum_L2' in H.
  rewrite /inr_or_def. done.

  eapply map_NI.
  eauto. eauto.
  instantiate (1:= eqpair state_type_equiv (out_equiv Opub Opriv)).
  mrw. intros.
  apply: rel_eqsum_L2.
  case/rel_eqpair: H;eauto.

  (*state update, under the slice invariant*)
  apply: policy_state_cell_NI.


  (*map*)
  eapply map_NI.
  instantiate (1:= eqmaybe_nobody (eqpair (eqsum (private_equiv Bool) (public_equiv _)) (eqmaybe_nobody (private_equiv _)))).
  mrw. intros.
  destruct i. destruct i'.
  rewrite !pair_rewr.
  apply rel_eqpair_R2' in H.
  destruct H. destruct H.
  remember H0. clear Heqr.
  move/eqsum_L_split : H0. case.
  move=>[]x0[]x1[]->[]->. auto.
  move=>[]x0[]x1[]->[]->Hout.
  apply rel_eqmaybe_nobody2.
  apply rel_eqpair2. con. rewrite !pair_rewr.

  move:H.
  move/rel_eqpair=>[] /rel_eqpair[]//.
  rewrite !pair_rewr.

  move:Hout.
  move/rel_eqpair=>[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] Hout _.
  move:Hout.
  case: x0=>a[]b[]c[]d[] e f.
  case: x1=>a'[]b'[] c'[] d'[] e' f'.
  rewrite !pair_rewr.
  move/rel_eqmaybe_nonbot. case.
  move=>[]x'[]y'[] ->[]->.
  rewrite /dI_out. intro. move: b0. simpl. case.
  case. intros. subst. auto. intros. auto.

  case.
  move=>[]x'[]y'[] ->[]->. intros. simpl. de e. case.
  move=>[]y'[] ->[]->. case. intros. subst. ssa.
  case. move=>->->. auto.
  case:H.
  destruct i0;last ssa.
  destruct i2;last ssa.
  auto.

  mrw. intros. destruct i. apply dis_eqpair_R in H. destruct i0;last ssa.
  rewrite !pair_rewr. done.

  by [].

  (*the slots, in pool order*)
  eapply maybe_NI.
  apply par_NI.
  exact: (@slot_visible_NI Empty Opub 5 _ _ (public_equiv _) _ _ erefl erefl (slot_no_input _) p_pub_NI).
  apply par_NI.
  exact: (@slot_visible_NI THandlerOutput Opriv 4 _ id (private_equiv _) (private_equiv _) _ erefl erefl (fun _ _ _ H => H) p_priv_NI).
  apply par_NI.
  exact: (@slot_visible_NI Empty Nat 3 _ _ (public_equiv _) _ _ erefl erefl (slot_no_input _) p_sched_NI).
  apply par_NI.
  exact: (@slot_hidden_NI Empty THandlerOutput 2 _ _ (public_equiv _) (private_equiv _) _ (slot_no_input _) ir_handler_private_NI).
  apply par_NI.
  exact: (@slot_hidden_NI Empty THandlerOutput 1 _ _ (public_equiv _) (private_equiv _) _ (slot_no_input _) ir_handler_private_NI).
  exact: (@slot_visible_NI Empty THandlerOutput 0 _ _ (public_equiv _) _ _ erefl erefl (slot_no_input _) ir_handler_public_NI).
Qed.

End Policy.

(* The sliced policy meets the three obligations. *)
Lemma model_sliced_NI : NI in_equiv (out_equiv Opub Opriv) (model_sliced runtime runs p_pub p_priv p_sched).
Proof.
apply: model_policy_NI.
- exact: sliced_init_gated.
- move=> o v; exact: sliced_service_gated.
- exact: sliced_service_NI.
Qed.

(* The timer-unmasked policy meets them too.  As for tick_slice, tick_unmasked
   reads only the counter. *)
Lemma queue_unmasked_rel l v v' :
  rel state_type_equiv l v v' ->
  rel state_type_equiv l (queue_unmasked v) (queue_unmasked v').
Proof.
  move=> H; rewrite /queue_unmasked.
  apply update_pending_rel; exact: unset_masks_rel.
Qed.

Lemma unmasked_service_NI :
  fv_NI (out_equiv Opub Opriv) state_type_equiv state_type_equiv (@unmasked_service runtime runs Opub Opriv).
Proof.
  rewrite /unmasked_service.
  apply fv_NI_comp; first exact: observe_timer_output_NI.

  mrw. intros.
  rewrite /tick_unmasked.

  have: get_slice_count v = get_slice_count v'.

  move: v H0=> [[cur prev]] [re_sched] [slice_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sched'] [slice_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H2=>/public_equiv_eq->//.
  move=>->.

  case: (get_slice_count v') => [|[|n]].
  - done.
  - by apply close_slice_rel.
  - case: (slice_at_boundary _ _).
    + by apply queue_unmasked_rel; apply update_slice_count_rel.
    + by apply update_slice_count_rel.
Qed.

Theorem model_timer_unmasked_NI : NI in_equiv (out_equiv Opub Opriv)
  (model_timer_unmasked runtime runs p_pub p_priv p_sched).
Proof.
apply: model_policy_NI.
- exact: sliced_init_gated.
- move=> o v; exact: unmasked_service_gated.
- exact: unmasked_service_NI.
Qed.


(* === Section 6 (payoff): the top result.  model_sliced_userview = map id
   parse_output model_sliced; NI is obtained from model_sliced_NI by output
   weakening through parse_output (out_equiv-related outputs map to
   out_equiv_userview-related ones).  (Paper, Section IV-B.) === *)
Lemma model_sliced_userview_NI : NI in_equiv (out_equiv_userview Opub Opriv) (model_sliced_userview runtime runs p_pub p_priv p_sched).
Proof.
  rewrite /model_sliced_userview /userview.
  eapply map_NI. eauto. eauto.
  2: apply model_sliced_NI.
  mrw. intros.
  move: H=> /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + +.
  move: i=>[a[] b[] c[] d[] e f].
  move: i'=>[a'[] b'[] c'[] d'[] e' f']. 
  rewrite !pair_rewr.
  rewrite /parse_output.
  move/rel_eqmaybe_all2. case.
  move=>[]x'[]y'[]->[]->/public_equiv_eq->//.
  move=>[]->->.
  move/rel_eqmaybe_all2. case.
  move=>[]x'[]y'[]->[]-> H _ _ _ _.
  apply rel_eqmaybe_all. ssa.
  move=>[]->[]->. auto.
Qed.

End Parametric.

End Parameters.


(* === The concrete system, recovered by instantiation. === *)
Corollary model_sliced_concrete_NI : NI in_equiv out_equiv_concrete model_sliced_concrete.
Proof.
  apply model_sliced_NI.
  apply p_pub_concrete_NI. apply p_priv_concrete_NI. apply scheduler_NI.
Qed.

Corollary model_sliced_userview_concrete_NI :
  NI in_equiv out_equiv_userviewC model_sliced_userview_concrete.
Proof.
  apply model_sliced_userview_NI.
  apply p_pub_concrete_NI. apply p_priv_concrete_NI. apply scheduler_NI.
Qed.  
