
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import RelationClasses.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
From HB Require Import structures.
From deriving Require Import deriving.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.DecidableClass.
Import Order.TTheory.
Open Scope order_scope.

Require Export NonInterference.theories.models.

(* ===================================================================
   NonInterference — the concrete security relations and the results.

   Prose companion: docs/noninterference.md (kept in sync with the
   section banners below).  Structure:
     4. Model interfaces : in_rel, out_rel (final_out_rel is in models.v)
     5. model_immediate is not non-interfering        (model_immediate_not_NI)
     6. model_sliced / wrapped are non-interfering (model_sliced_NI, model_sliced_userview_NI)
     7. The state relation (stateType_rel) and the fv_NI obligation
   Note: this file imports classical logic via theorems.v (Require Import
   Classical), used only in swi_NI' because `aware` is not constructively
   decidable.
   =================================================================== *)

(* --- Section 4: input relation.  in_rel = TInterrupt_rel is a CUSTOM
   relation: ir_dis makes ONLY the disk interrupt secret, and only at bot;
   the timer interrupt stays public.  (docs/noninterference.md §4.) --- *)
Definition ir_dis (l : level) (ir : [TInterrupt]) := ir = DiskInterrupt /\ l = \bot.
Definition TInterrupt_rel : cRel [TInterrupt].
  refine (@CRel _
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


Definition in_rel : cRel [T_in] := TInterrupt_rel.

(* out_rel: the 6-slot pool output.  Handler slots are default/NOP, disk,
   timer: the first two are secret (eqmaybe_top privateRel), the timer slot
   is public (it reacts only to public timer interrupts). *)
Definition out_rel : cRel [T_out'] := eqpair (eqmaybe (publicRel _))
                                          (eqpair (eqmaybe (privateRel _))
                                             (eqpair (eqmaybe (publicRel _))
                                                (eqpair (eqmaybe_top ((privateRel _)))
                                                   (eqpair (eqmaybe_top (privateRel _))
                                                      (eqmaybe (publicRel _)))))).

Lemma Trace_imp : forall (A B : Ty) (p : Proc A B) (s : seq ([A] + [B])) l (BRel BRel' : cRel [B]), (forall x y, rel BRel l x y -> rel BRel' l x y) -> Trace BRel l s p -> Trace BRel' l s p.
Proof.  
  intros.
  elim : H0 H;ssa.
  econ. eauto. eauto.
  econ;eauto.
Qed.

Lemma helper_trace' : Trace (publicRel _) \bot [::out_get';out_get'] model_immediate.
Proof.
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

Lemma helper_trace : Trace out_rel \bot [::out_get';out_get'] model_immediate.
Proof.
  eapply Trace_imp. 2:eapply helper_trace'.
  intros. simpl in H. subst. auto.
Qed.  


(*Opaque otherwise the inversion tactic take forever*)
Opaque state_step pool_input initial_state def f_proj.

(* === Section 5: model_immediate is not non-interfering.  Witness: a short
   bot-trace of two public requests; insert a disk interrupt at the front
   (secret at bot); its pending flag reschedules the disk handler, which then
   runs its full two steps, so the expected second public output becomes None.
   Two public outputs suffice to refute NI.  Short by necessity —
   inversion on reductions is expensive.  (docs/noninterference.md §5.) === *)
Lemma model_immediate_not_NI : ~ NI in_rel out_rel model_immediate.
Proof.
  intro. rewrite /NI in H. move: (H \bot). clear H.
  rewrite /NI_l. case=>_ [] + _. intros.
  move: helper_trace.
  move/a. move/(_ (DiskInterrupt) 0). simpl.
  have: ir_dis \bot DiskInterrupt. ssa.
  move=>aa. move/(_ aa).
  move=>Htr. clear a aa.
  inv Htr;clear Htr;match_dd. 
  rewrite /= in x. clear x.
  inv H3;clear H3;match_dd. ssa.
  inv H5;clear H5;match_dd.
  move: H9. clear. simpl. ssa.
Qed.

Transparent pool_input initial_state def f_proj.


(*The rest of the file shows nonintereference of model2 and model3*)

Lemma eqsum_L_llrr l i i' : rel (eqsum_L in_rel out_rel) l i i' -> is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'.
Proof.
  intros. destruct i. destruct i'. ssa.
  exfalso. ssa. destruct i'. ssa. ssa.
Qed.

Lemma eqsum_llrr  (A B : Ty) (ARel : cRel [A]) (BRel : cRel [B])  l i i' : rel (eqsum ARel BRel) l i i' -> is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'.
Proof.
  intros. destruct i. destruct i'. ssa.
  exfalso. ssa. destruct i'. ssa. ssa.
Qed.

Lemma eqsum_split (A B : Ty) (ARel : cRel [A]) (BRel : cRel [B]) l i0 i1 : rel (eqsum ARel BRel) l i0 i1 -> (exists i0' i1', (i0 = inl i0' /\ i1 = inl i1' /\ rel ARel l i0' i1')) \/
                                                                                                              exists i0' i1', (i0 = inr i0' /\ i1 = inr i1' /\ rel BRel l i0' i1').
Proof.
  intros. apply eqsum_llrr in H as H'. destruct H'.
  destruct H0. destruct i0. destruct i1.
  left. exists i. exists i0. ssa.
  ssa. ssa. destruct i0. ssa.
  destruct i1. ssa.
  right. exists i. exists i0. ssa.
Qed.

Lemma private_not_bot : forall (A : Ty) l (x y : [A]), l <> \bot -> x = y -> rel (privateRel _) l x y.
Proof.
ssa.
Qed.

Lemma private_not_bot' : forall (A : Ty) l (x y : [A]), l <> \bot -> rel (privateRel _) l x y -> x = y.
Proof.
ssa. de H0.
Qed.

Lemma eqmaybe_private_not_bot' : forall (A : Ty) l (x y : [Option A]), l <> \bot -> rel (eqmaybe (privateRel _)) l x y -> x = y.
Proof.
ssa. de x. de y. de H0. subst. done. de y.
Qed.

Lemma eqmaybe_public_not_bot : forall (A : Ty) l (x y : [Option A]), l <> \bot -> rel (eqmaybe (publicRel _)) l x y -> x = y.
Proof.
ssa. de x. de y. subst. done. de y.
Qed.

Lemma eqmaybe_private_not_bot : forall (A : Ty) l (x y : [Option A]), l <> \bot -> rel (eqmaybe_top (privateRel _)) l x y -> x = y.
Proof.
ssa. de x. de y. de H0. subst. done. de y.
Qed.

Lemma eqmaybe_private_bot : forall (A : Ty) (x y : [Option A]), rel (eqmaybe_top (privateRel _)) \bot x y.
Proof.
  ssa. de x. de y. de y.
Qed.

Lemma private_bot : forall (A : Ty) (x y : [A]), rel ((privateRel _)) \bot x y.
Proof.
  ssa.
Qed.

Hint Resolve private_bot.

Lemma publicRel_eq : forall (A : Ty) l x y, rel (publicRel A) l x y -> x = y.
Proof. ssa. Qed.

Lemma out_rel_not_bot : forall i i' l, l <> \bot -> rel out_rel l i i' -> i = i'.
Proof.
  intros.
  move:H0. move/rel_eqpair=> [] + /rel_eqpair [] + /rel_eqpair [] + /rel_eqpair [] + /rel_eqpair [].
  move: i=>[a [b [c [d [e f]]]]].
  move: i'=>[a' [b' [c' [d' [e' f']]]]].  
  rewrite !pair_rewr.
  move=>/eqmaybe_public_not_bot=>->//.
  move=>/eqmaybe_private_not_bot'=>->//.
  move=>/eqmaybe_public_not_bot=>->//.
  move/rel_eqmaybe_top.
  case.
  move=>[x0][y0][]->[]-> /private_not_bot' ->//.
  move=>/eqmaybe_private_not_bot=>->//.
  move=>/eqmaybe_public_not_bot=>->//.
  case. ssa.
  case. ssa.
  move=>[]->->.
  move=>/eqmaybe_private_not_bot=>->//.
  move=>/eqmaybe_public_not_bot=>->//.  
Qed.



Lemma falseRel_aware : forall l, aware falseRel true l.
Proof.
intros. rewrite /aware. intros. ssa. subst. simpl. intro. ssa.
Qed.

(* === Section 7a: the state relation.  Classification across two bot-related
   states: masks PUBLIC everywhere; the secret handlers' (disk, default)
   pending bits secret via hidden_pending; cur_pid's inl/inr tag PUBLIC but the
   bool inside inl (which handler) secret;
   re_sch, ir_count (the slice), scheduler/user pid all public.
   (docs/noninterference.md §7a.) === *)
Definition pids_rel : cRel [pids] := eqpair (eqsum (privateRel _) (publicRel _)) (publicRel _).
Definition hidden_pending : cRel [I_bits] := eqpair (privateRel _) (publicRel _).
Definition public_pair : cRel [I_bits] := eqpair (publicRel _) (publicRel _).
Definition ic_rel : cRel [ic] := eqpair hidden_pending (eqpair hidden_pending public_pair).
Definition bool_state_rel : cRel [bool_state] := eqpair (publicRel _) (eqpair (publicRel _) ic_rel).
Definition stateType_rel : cRel [stateType] := eqpair pids_rel bool_state_rel.


Lemma stateType_rel_not_bot : forall i i' l, l <> \bot -> rel stateType_rel l i i' -> i = i'.
Proof.
  intros.
  move:H0.
  move/rel_eqpair=> [] /rel_eqpair[] + + /rel_eqpair [] + /rel_eqpair [] + /rel_eqpair [] /rel_eqpair [] + + /rel_eqpair[] /rel_eqpair[] + + /rel_eqpair [] + +.
  move: i=>[[a0 a1]] [b [b0 [[b1 b2 [[b3 b4 [b5 b6]]]]]]].
  move: i'=>[[a0' a1']] [b' [b0' [[b1' b2' [[b3' b4' [b5' b6']]]]]]].  
  rewrite !pair_rewr. 
  move=> /eqsum_split Hsplit.
  move=>/publicRel_eq -> /publicRel_eq -> /publicRel_eq -> // /private_not_bot' -> // /publicRel_eq -> // /private_not_bot' -> // /publicRel_eq -> // /publicRel_eq -> /publicRel_eq ->.
  case: Hsplit.
  move=>[x][y][]->[]->/private_not_bot' ->//.
  move=>[x][y][]->[]-> /publicRel_eq ->//.  
Qed.


Transparent state_step pool_input initial_state def f_proj.

Lemma in_rel_eq i i0 l : rel in_rel l i i0 -> i = i0.
Proof.
  ssa. de H. move: H H0. rewrite /ir_dis. ssa. subst. done.
Qed.

Lemma sta_comp : forall (I V O : Ty) (IRel : cRel [I]) (VRel : cRel [V]) (ORel : cRel [O]) (f f' : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V])
                        (v : [V]) (p : Proc (Times V I) O),
    fv_NI ORel VRel VRel g ->
    fv_NI IRel VRel VRel f -> f_EP IRel VRel f ->
    fv_NI IRel VRel VRel f' -> f_EP IRel VRel f' ->
    NI (eqpair_R VRel IRel) ORel p ->    
    NI IRel (eqpair VRel ORel) (sta (fun i => (f i) \o (f' i)) g v p).
Proof.
  intros.
  apply sta_NI;eauto.
  move: H0 H2. clear.
  rewrite /fv_NI. intros. eauto.
  move: H1 H3. clear.
  rewrite /f_EP. intros. eauto.
Qed.


(* === Section 7b: the composition-breakdown technique.  state_step is
   initiate_next(bool_coding) o handler_preroutine o step1 o step0.  fv_NI_comp
   discharges fv_NI of the composition from fv_NI of the parts; fv_NI_step_left
   / _right lift each stage to the eqsum in_rel/out_rel event.  Cost: every
   stage is proved over ALL related states, forgetting the reachable subset —
   bool_coding (7c) repairs this before initiate_next.  (docs §7b.) === *)
Lemma fv_NI_comp : forall (I V: Ty) (IRel : cRel [I]) (VRel : cRel [V]) (f f' : [I]  -> [V] ->  [V]),
    fv_NI IRel VRel VRel f -> fv_NI IRel VRel VRel f' -> fv_NI IRel VRel VRel (fun i => (f' i) \o (f i)).
Proof.
intros. move: H H0. rewrite /fv_NI. ssa.
Qed.

Lemma f_EP_comp : forall (I V: Ty) (IRel : cRel [I]) (VRel : cRel [V]) (f f' : [I]  -> [V] ->  [V]),
    f_EP IRel VRel f -> f_EP IRel VRel f' -> f_EP IRel VRel (fun i => (f' i) \o (f i)).
Proof.
intros. move: H H0. rewrite /f_EP. ssa. eauto.
Qed.

Lemma fv_NI_step_left : forall f,
    fv_NI in_rel stateType_rel stateType_rel f -> fv_NI (eqsum in_rel out_rel) stateType_rel stateType_rel (step_left f).
Proof.
  ssa. move: H. mrw. intros.
  apply eqsum_llrr in H0 as H0'. destruct H0'. destruct H2. destruct i. destruct i'.
  rewrite /step_left. eauto. done. done.
  destruct H2. destruct i. done. destruct i'. done.
  rewrite /step_left. eauto.
Qed.

Lemma fv_NI_step_right : forall f,
    fv_NI out_rel stateType_rel stateType_rel f -> fv_NI (eqsum in_rel out_rel) stateType_rel stateType_rel (step_right f).
Proof.
  ssa. move: H. mrw. intros.
  apply eqsum_llrr in H0 as H0'. destruct H0'. destruct H2. destruct i. destruct i'.
  rewrite /step_left. eauto. done. done.
  destruct H2. destruct i. done. destruct i'. done.
  rewrite /step_left. eauto.
Qed.

Lemma f_EP_left : forall f,
    f_EP in_rel stateType_rel f -> f_EP (eqsum in_rel out_rel) stateType_rel (step_left f).
Proof.
  ssa.
Qed.

Lemma f_EP_right : forall f,
    f_EP out_rel stateType_rel f -> f_EP (eqsum in_rel out_rel) stateType_rel (step_right f).
Proof.
  ssa.
Qed.

Definition ready_aux (v : [stateType]) := I_ready v TimerInterrupt /\ first_ready v = Some TimerInterrupt \/ ~ I_ready v TimerInterrupt /\ I_ready v DiskInterrupt /\ first_ready v = Some DiskInterrupt \/  ~ I_ready v TimerInterrupt /\ ~ I_ready v DiskInterrupt /\ I_ready v DefaultInterrupt /\ first_ready v = Some DefaultInterrupt \/ ~ I_ready v TimerInterrupt /\ ~ I_ready v DiskInterrupt /\ ~ I_ready v DefaultInterrupt /\ first_ready v = None.

Lemma ready_auxP v : ready_aux v.
Proof.
  rewrite /ready_aux.
  destruct (I_ready v TimerInterrupt) eqn:Heqn. left. ssa.
  rewrite /first_ready. rewrite /all_interrupts /ohead. rewrite /filter.
  rewrite Heqn. done.
  right.
  destruct (I_ready v DiskInterrupt) eqn:Heqn'.
  left. con. done. con. done.
  rewrite /first_ready /ohead /filter /all_interrupts Heqn Heqn' //.
  right.
  destruct (I_ready v DefaultInterrupt) eqn:Heqn''.
  left. con. done. con. done. con. done.
  rewrite /first_ready /ohead /filter /all_interrupts Heqn Heqn' Heqn''//.
  rewrite /first_ready /ohead /filter /all_interrupts Heqn Heqn' Heqn''//. ssa.
Qed.


Definition ready_cases (v v' : [stateType]) := ready_aux v /\ ready_aux v'.

Definition ready_aux2 (v : [stateType]) := I_ready v DiskInterrupt /\ first_ready v = Some DiskInterrupt \/
                                             ~ I_ready v DiskInterrupt /\ I_ready v DefaultInterrupt /\ first_ready v = Some DefaultInterrupt \/
                                             ~ I_ready v DiskInterrupt /\ ~ I_ready v DefaultInterrupt /\ first_ready v = None.

Definition ready_cases2 (v v' : [stateType]) := I_ready v TimerInterrupt /\ I_ready v' TimerInterrupt /\ first_ready v = Some TimerInterrupt /\ first_ready v' = Some TimerInterrupt \/
                                                  ~ I_ready v TimerInterrupt /\ ~ I_ready v' TimerInterrupt /\
                                                    ready_aux2 v /\ ready_aux2 v'.

Lemma ready_casesP v v' : ready_cases v v'.
Proof.
  rewrite /ready_cases. con. apply ready_auxP. apply ready_auxP.
Qed.

Lemma ready_cases2P v v' : I_ready v TimerInterrupt = I_ready v' TimerInterrupt -> ready_cases2 v v'.
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

Lemma first_ready_update_re_sch : forall v b, first_ready (update_re_sch v b) = first_ready v.
Proof.
  intros. cbv. ssa.
Qed.

(* === Leaf obligations for the three replaceable slots ===

   The pool's userspace and scheduler slots are discharged by these three
   facts and nothing else.  Stating them separately makes explicit what the
   assembled proof needs of each slot: an NI process at the classification
   its slot declares.  (docs/noninterference.md) *)

(* Slot 5, the public user process.  Its output slot is public, so it may
   emit anything as long as it emits it unconditionally. *)
Lemma low_p_NI : forall (IRel : cRel [Empty]), NI IRel (publicRel TPublicOutput) low_p.
Proof.
  intros. apply out_NI.
Qed.

(* Slot 4, the secret user process.  Both its input (the disk handler's
   [Notify]) and its output are secret. *)
Lemma high_p_NI : NI (privateRel THandlerOutput) (privateRel TTypeSyscall) high_p.
Proof.
  eapply map_NI.
  mrw. intros. apply rel_eqsum_L. eauto.
  mrw. intros. apply dis_eqsum_L. done.
  mrw. intros. move: H.
  instantiate (1:= eqsum_L _ _). intros.
  destruct i. destruct i'. apply rel_refl. ssa.
  destruct i'. ssa.
  apply rel_eqsum_R2' in H.
  destruct i. destruct i0.
  2: apply loop_NI.
  destruct i1. destruct i2.
  move:H. instantiate (1:=  (eqpair (privateRel Bool) _)).
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
  Unshelve. all: exact (publicRel _).
Qed.

(* Slot 3, the scheduler.  Its output -- the pid it picks -- is public. *)
Lemma scheduler_NI : forall (IRel : cRel [Empty]), NI IRel (publicRel Nat) scheduler.
Proof.
  intros.
  eapply map_NI. eauto. eauto.
  instantiate (1:=eqpair _ _).
  mrw. move=> l i i' /rel_eqpair[] + _.
  instantiate (1:= publicRel _). move=>/publicRel_eq ->. ssa.
  eapply sta_NI.
  mrw. intros. move: H0.
  move/publicRel_eq=>->//.
  mrw. intros. eauto.
  mrw. intros. auto.
  apply out_NI.
  Unshelve. all: exact (publicRel _).
Qed.



(* === Section 6: model_sliced is non-interfering.  Assembled from the generic
   composition theorems (par_NI, sta_NI, swi_NI, map/output-weakening) applied
   to the pool; the only non-mechanical obligation is fv_NI of the state
   transition (section 7).  (docs/noninterference.md §6.)

   The result holds for *any* scheduler and any two user processes that are
   themselves non-interfering at the classification their slot declares.  That
   it can: [state_step] never reads a user process's output value, only whether
   the slot produced one -- [is_sch_out] matches [(None,(None,(Some n,_)))] --
   so no user behaviour reaches the schedule, and fv_NI, the one hard
   obligation, does not depend on which processes fill the slots.

   [low_p_NI], [high_p_NI] and [scheduler_NI] above are the instances that give
   back the concrete system; see the corollaries at the end of the file. === *)

(* The parametric proof cannot unfold its own processes, so [rewr] drops
   /low_p /alternate /high_p /scheduler. *)
Ltac rewr ::= rewrite /model_sliced /reactive_system /pool /process_pool /my_f_initial /slot_procs /pool_input /tI_o /I_handler /f_proj /low_out.

Section Parametric.

Variable p_pub : Proc Empty TPublicOutput.
Variable p_priv : Proc THandlerOutput TTypeSyscall.
Variable p_sched : Proc Empty Nat.

Hypothesis p_pub_NI : forall IRel : cRel [Empty], NI IRel (publicRel TPublicOutput) p_pub.
Hypothesis p_priv_NI : NI (privateRel THandlerOutput) (privateRel TTypeSyscall) p_priv.
Hypothesis p_sched_NI : forall IRel : cRel [Empty], NI IRel (publicRel Nat) p_sched.

Lemma model_sliced_NI : NI in_rel out_rel (model_sliced p_pub p_priv p_sched).
Proof.
  rewr;simpl;rewr;simpl.
  eapply map_NI.
  instantiate (1:= eqsum_L in_rel out_rel). ssa. ssa.
  mrw. intros.
  2:eapply loop_NI. apply eqsum_L_llrr in H as H'. destruct H'.
  destruct i. destruct i'. ssa. ssa. ssa.
  destruct i. ssa. destruct i'. ssa.
  apply rel_eqsum_L2' in H. 
  rewrite /inr_or_def. done.

  eapply map_NI.
  eauto. eauto.
  mrw. intros.
  case/rel_eqpair: H;eauto.
  instantiate (1:= stateType_rel).

  (*state update: This part is long. Involves step0, step1, step2*)
  apply sta_NI.
  mrw;eauto.

  apply fv_NI_comp.

  (*step0*)
  rewrite /step0.
  apply fv_NI_step_left.

  mrw. intros.
  apply in_rel_eq in H;subst.
  move: H0.
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[]H2 /rel_eqpair[]/rel_eqpair[]H3 H4/rel_eqpair[]/rel_eqpair[]H5 H6/rel_eqpair[]H7 H8.
  move: H0 H1 H2 H3 H4 H5 H6 H7 H8.
  move: v=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].
  rewrite /get_ic /update_ic /get_bool_state /update_bool_state /get_I_mask /get_mask' /update_I_pending /update_I_bits /update_I_bits' !pair_rewr.
  move=> H0 H1 H2 H3 H4 H5 H6 H7 H8.
  rewrite /get_ic /update_ic /get_bool_state /update_bool_state /get_I_mask /get_mask' /update_I_pending /update_I_bits /update_I_bits' !pair_rewr.    

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

  apply fv_NI_comp.

  (*step1*)
  rewrite /step1.
  apply fv_NI_step_right. rewrite /check_scheduler.

  mrw. intros.

  destruct (eqVneq l \bot).
  2: {  apply out_rel_not_bot in H. 2:apply/eqP=>//. subst.
        apply stateType_rel_not_bot in H0. 2:apply/eqP=>//. subst. eauto. }
  subst.  

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] /publicRel_eq H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6. 
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H=> /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] _ /rel_eqpair[] _ +.
  move: i=>[a[] b[] c[] d[] e f].
  move: i'=>[a'[] b'[] c'[] d'[] e' f']. 
  rewrite !pair_rewr /is_sch_out. subst.
 
  case/rel_eqmaybe2.
  move=>[]x []y []-> []->// /publicRel_eq ->//.
  move=>[]->[]->//.

  case/rel_eqmaybe2.
  move=>[]x' []y' []-> []->// Hpr.
  move=>[]->[]->//.

  case/rel_eqmaybe2.
  move=>[]x0 []y0 []-> []->// /publicRel_eq ->//.

  move=>_. (*drop*)

  apply/rel_eqpair2;con;try solve [ssa].

  move=>[]->[]->//.


  (*step1*)
  apply fv_NI_comp.
  
  apply fv_NI_step_right.

  apply fv_NI_comp.

  mrw. intros.
  rewrite /initiate_ir.

  have: tI_out i = tI_out i'.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H=> /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ +.
  move: i=>[a[] b[] c[] d[] e f].
  move: i'=>[a'[] b'[] c'[] d'[] e' f']. 
  rewrite !pair_rewr /is_sch_out.  

  case/rel_eqmaybe2.
  move=>[]x'[]y'[]->[]->/publicRel_eq->//.
  move=>[]->->//.

  move=>->.

  destruct ((tI_out i')). destruct h. done.
  apply/rel_eqpair2. con;ssa. done.


  apply fv_NI_comp.
  mrw. intros.
  rewrite /check_handler_completed.

  have: get_ir_count v = get_ir_count v'.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H2=>/publicRel_eq->//.
  move=>->.
  destruct (handler_completed (get_ir_count v')).

  apply/rel_eqpair2. con. ssa.
  apply/rel_eqpair2. con. ssa.  
  apply/rel_eqpair2. con. ssa.
  apply/rel_eqpair2. con. 
  apply/rel_eqpair2. con. ssa. eauto.
  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. ssa. eauto.
  apply/rel_eqpair2. con. ssa. ssa. done.

  mrw. intros.
  rewrite /check_ir_count.

  have: get_ir_count v = get_ir_count v'.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H2=>/publicRel_eq->//.
  move=>->.

  destruct (get_ir_count v').
  destruct n.

  apply/rel_eqpair2. con. ssa.
  apply/rel_eqpair2. con. ssa.  
  apply/rel_eqpair2. con. ssa.
  apply/rel_eqpair2. con. 
  apply/rel_eqpair2. con. ssa. eauto.
  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. ssa. eauto.
  apply/rel_eqpair2. con. ssa. ssa.

  apply/rel_eqpair2. con. ssa.
  apply/rel_eqpair2. con. ssa.  
  apply/rel_eqpair2. con. ssa.
  apply/rel_eqpair2. con. 
  apply/rel_eqpair2. con. ssa.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    rewrite !pair_rewr.

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6. eauto.
  
  apply/rel_eqpair2. con. ssa.
  apply/rel_eqpair2. con. ssa. ssa. done.

  mrw. intros.
  destruct (eqVneq l \bot).
  2: { move/eqsum_split : H. case.
       move=>[]x[]y[]->[]->. ssa.
       move=>[]x[]y[]->[]->. 
       apply stateType_rel_not_bot in H0. 2:apply/eqP=>//. subst. eauto.
  }

  subst.

  move/eqsum_split: H. case.
  move=>[]x[]y[]->[]->. ssa.
  move=>[]x[]y[]->[]->. move=>Hout.
  rewrite /step_right.

  rewrite /initiate_next.

  have: masks_set v = masks_set v'.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask']. 

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H4 H5 H6.
  move=>/publicRel_eq ->.
  move=>/rel_eqpair[] _. rewrite !pair_rewr=> /publicRel_eq ->.
  move=>/rel_eqpair[] _. rewrite !pair_rewr=> /publicRel_eq ->. ssa.
  move=>->.
  
  destruct (masks_set v'). done. 

  have: I_ready  (bool_coding v) TimerInterrupt =
          I_ready (bool_coding v') TimerInterrupt. 


  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H6. move/rel_eqpair=>[]. rewrite !pair_rewr. move=>/publicRel_eq->/publicRel_eq->.
  move/publicRel_eq : H2=>->//. 
  
  move/ready_cases2P. rewrite /ready_cases2.

  move=>[[]Hready[]Hready'[]Hfirst Hfirst'|[]Hready[]Hready'[]Haux Haux'].
  rewrite Hfirst Hfirst'.

  clear Hready Hready' Hfirst Hfirst'.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.  

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con.
  rewrite /initiate_handler !pair_rewr. ssa.

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.  
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.  
  
  move:Haux Haux'.
  rewrite /ready_aux2.
  move=>[[]HreadyD Hfirst|].
  move=>[[]HreadyD' Hfirst'|[]].
  rewrite Hfirst Hfirst'.


  clear Hready Hready' Hfirst Hfirst' HreadyD HreadyD'.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.  

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con.
  rewrite /initiate_handler !pair_rewr. ssa. 

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  apply/rel_eqpair2. con.

  move/publicRel_eq : H2=>->.
  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.  
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. eauto. ssa.
  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. eauto. ssa.
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H6. case. rewrite !pair_rewr. move=>/publicRel_eq->//. 
  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->//. 
  move=>[]i0'[]i1'[]->[]-> /publicRel_eq ->/publicRel_eq ->. ssa.

  move/publicRel_eq : H4=>->//.

  move=>[]HreadyD'[]HreadyDef' Hfirst'.
  rewrite Hfirst Hfirst'.

  clear Hready Hready' Hfirst Hfirst' HreadyD HreadyD' HreadyDef'.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.  

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con.
  rewrite /initiate_handler !pair_rewr. ssa. 

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  apply/rel_eqpair2. con.

  move/publicRel_eq : H2=>->.
  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.  
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. eauto. ssa.
  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. eauto. ssa.
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H6. case. rewrite !pair_rewr. move=>/publicRel_eq->//. 
  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->//. 
  move=>[]i0'[]i1'[]->[]-> /publicRel_eq ->/publicRel_eq ->. ssa.

  move/publicRel_eq : H4=>->//.


  move=>[]HreadyD'[]HreadyDef' Hfirst'.
  rewrite Hfirst Hfirst'. exfalso.
  clear Hready Hready' Hfirst Hfirst'.
  
  move: v H0 HreadyD HreadyD' HreadyDef'=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[_] /rel_eqpair[_] /rel_eqpair[] HH /rel_eqpair[]/rel_eqpair[_ H4] /rel_eqpair[] /rel_eqpair[] _ H5 /rel_eqpair[] _ H6.
  rewrite !pair_rewr in HH H4 H5 H6.  
  move: HH H4 H5 H6. move=>/publicRel_eq->/publicRel_eq->/publicRel_eq->/publicRel_eq->. 

  rewrite /I_ready /get_I_pending /get_pending' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /bool_coding /get_I_mask /get_mask' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /update_bool_state !pair_rewr /timeslice_live /get_ir_count /get_ic_count /get_bool_state !pair_rewr.
  move=>+ /negP + /negP.
  rewrite !negb_and !negbK.
  move/andP. case.
  rewrite orbC [ false || _ ]/orb.
  move=>Hpending.
  rewrite !negb_or !negbK.
  move/andP. case. move=>Hmask Hir.
  move/orP. case.
  simpl. move/orP. case.
  move=>HH. move/orP. case.
  move/andP. ssa. ssa. apply/negP. apply H0. done. 
  move/orP. case. intro. apply/negP. apply Hmask. done.
  intro. apply/negP. apply b. done. done.
  move/orP. case. intro. rewrite a in Hmask. done.
  rewrite Hir. done.

  move=>[[]HreadyD[]HreadyDef Hfirst|].
  move=>[[]HreadyD' Hfirst'|].
  rewrite Hfirst Hfirst'.

  clear Hready Hready' Hfirst Hfirst' HreadyD HreadyD' HreadyDef.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.  

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con.
  rewrite /initiate_handler !pair_rewr. ssa. 

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  apply/rel_eqpair2. con.

  move/publicRel_eq : H2=>->.
  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.  
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. eauto. ssa.
  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. eauto. ssa.
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H6. case. rewrite !pair_rewr. move=>/publicRel_eq->//. 
  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->//. 
  move=>[]i0'[]i1'[]->[]-> /publicRel_eq ->/publicRel_eq ->. ssa.

  move/publicRel_eq : H4=>->//.  
  

  move=>[[]HreadyD'[]HreadyDef' Hfirst'|].
  rewrite Hfirst Hfirst'.

  clear Hready Hready' Hfirst Hfirst' HreadyD HreadyD' HreadyDef HreadyDef'.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.  

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con.
  rewrite /initiate_handler !pair_rewr. ssa. 

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  apply/rel_eqpair2. con.

  move/publicRel_eq : H2=>->.
  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.  
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->. rewrite !pair_rewr //.
  move/publicRel_eq : H1=>->//.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->/publicRel_eq ->. rewrite !pair_rewr //.

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. eauto. ssa.
  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. eauto. ssa.
  apply/rel_eqpair2. con.

  move/rel_eqpair2 : H6. case. rewrite !pair_rewr. move=>/publicRel_eq->//. 
  move/rel_eqpair2 : H0=>[]. rewrite !pair_rewr.
  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_/publicRel_eq ->//. 
  move=>[]i0'[]i1'[]->[]-> /publicRel_eq ->/publicRel_eq ->. ssa.

  move/publicRel_eq : H4=>->//.  

  move=>[]HreadyD'[]HreadyDef' Hfirst'.
  rewrite Hfirst Hfirst'. exfalso.

  clear Hready HreadyD Hready' Hfirst Hfirst'.
  
  move: v H0 HreadyD' HreadyDef HreadyDef'=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[_] /rel_eqpair[_] /rel_eqpair[] HH /rel_eqpair[]/rel_eqpair[_ H4] /rel_eqpair[] /rel_eqpair[] _ H5 /rel_eqpair[] _ H6.
  rewrite !pair_rewr in HH H4 H5 H6.  
  move: HH H4 H5 H6. move=>/publicRel_eq->/publicRel_eq->/publicRel_eq->/publicRel_eq->. 

  rewrite /I_ready /get_I_pending /get_pending' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /bool_coding /get_I_mask /get_mask' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /update_bool_state !pair_rewr /timeslice_live /get_ir_count /get_ic_count /get_bool_state !pair_rewr.
  rewrite /I_ready /get_I_pending /get_pending' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /bool_coding /get_I_mask /get_mask' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /update_bool_state !pair_rewr /timeslice_live /get_ir_count /get_ic_count /get_bool_state.  
  move/negP. rewrite !negb_and !negbK.
  move/orP. case. move/orP. case.
  intro.
  move/andP. case. move/orP. case.
  move=>b.
  rewrite negb_or negbK. move/andP.
  case. move=>c d.
  move/negP. rewrite negb_and negb_or.
  move/orP. case. rewrite d. ssa. rewrite d. ssa.
  rewrite negb_and negbK orbC /=in b0.
  by rewrite b0 in c.
  move=>->.  rewrite negb_or negbK.
  move/andP. case.
  move=>b c. move/negP.
  rewrite negb_and negb_or.
  move/orP. case. ssa.
  rewrite negb_and b. ssa. ssa.
  move/orP. case.
  move=>a. move/andP. case.
  move/orP. case. move=>b.
  rewrite !negb_or !negbK. move/andP. case.
  rewrite a. ssa.
  move=>b. rewrite !negb_or !negbK.
  move/andP. case. rewrite a. ssa.
  move=>a. move/andP. case. move/orP. case.
  move=>b. rewrite !negb_or negbK.
  move/andP. case. move=>c.
  move=>d. rewrite d in a. done.
  move=>b. rewrite b in a. done.

  move=>[]HreadyD[]HreadyDef Hfirst.
  move=>[[]HreadyD'[]Hfirst'|].
  rewrite Hfirst Hfirst'. exfalso.

  clear Hready Hready' Hfirst Hfirst'.
  
  move: v H0 HreadyD' HreadyD HreadyDef => [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[_] /rel_eqpair[_] /rel_eqpair[] HH /rel_eqpair[]/rel_eqpair[_ H4] /rel_eqpair[] /rel_eqpair[] _ H5 /rel_eqpair[] _ H6.
  rewrite !pair_rewr in HH H4 H5 H6.  
  move: HH H4 H5 H6. move=>/publicRel_eq->/publicRel_eq->/publicRel_eq->/publicRel_eq->. 

  rewrite /I_ready /get_I_pending /get_pending' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /bool_coding /get_I_mask /get_mask' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /update_bool_state !pair_rewr /timeslice_live /get_ir_count /get_ic_count /get_bool_state !pair_rewr.
  rewrite /I_ready /get_I_pending /get_pending' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /bool_coding /get_I_mask /get_mask' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /update_bool_state !pair_rewr /timeslice_live /get_ir_count /get_ic_count /get_bool_state.  
  move/andP. case. intro.
  rewrite negb_or negbK. move/andP. case.
  intro. intro.
  move/negP. rewrite negb_and negb_or.
  move/orP. case. move/andP. case.
  move=> c _.
  move/negP. rewrite negb_and negb_or.
  move/orP. case. move/andP. case.
  intro. rewrite b. done. rewrite negb_and negbK.
  move/orP. case. intro. rewrite a1 in a0. done.
  rewrite b. done. rewrite negb_and negbK.
  move/orP. case. intro. rewrite a1 in a0. done.
  rewrite b. done.

  move=>[[]HreadyD'[]HreadyDef' Hfirst'|].
  rewrite Hfirst Hfirst'. exfalso.

  clear Hready Hready' Hfirst Hfirst'.
  
  move: v H0 HreadyD' HreadyD HreadyDef HreadyDef' => [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[_] /rel_eqpair[_] /rel_eqpair[] HH /rel_eqpair[]/rel_eqpair[_ H4] /rel_eqpair[] /rel_eqpair[] _ H5 /rel_eqpair[] _ H6.
  rewrite !pair_rewr in HH H4 H5 H6.  
  move: HH H4 H5 H6. move=>/publicRel_eq->/publicRel_eq->/publicRel_eq->/publicRel_eq->. 

  rewrite /I_ready /get_I_pending /get_pending' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /bool_coding /get_I_mask /get_mask' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /update_bool_state !pair_rewr /timeslice_live /get_ir_count /get_ic_count /get_bool_state !pair_rewr.
  rewrite /I_ready /get_I_pending /get_pending' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /bool_coding /get_I_mask /get_mask' /get_I_bits /get_I_bits' /get_ic /get_ic_count /get_bool_state /update_bool_state !pair_rewr /timeslice_live /get_ir_count /get_ic_count /get_bool_state.

  move/negP. rewrite !negb_and !negb_or.
  move/orP. case. intro.

  move/negP. rewrite ?negb_and ?negb_or.
  move/orP. case. intro.

  move/negP. rewrite ?negb_and ?negb_or.
  move/orP. case. move/andP. case. intro. intro.

  move/andP. case. move/orP. case. intro.
  move/andP. case. intro. rewrite b. done.
  intro. rewrite b0 in b. done.
  rewrite !negbK.
  move/orP. case. intro.
  move/andP. case.
  move/orP. case. intro.
  move/andP. case. intro. rewrite a1 in a3. done.
  intro.
  rewrite b a1. done.
  intro. move/andP. case.
  move/orP. case. intro.
  move/andP. case. intro. intro. rewrite b0 in b. done.
  intro. rewrite b0 in b. done.
  rewrite !negbK. move/orP. case. intro.
  move/negP. rewrite !negb_and !negb_or.
  move/orP. case. move/andP. case. intro.
  intro. move/andP. case. move/orP. case.
  intro. move/andP. case. intro.
  intro. rewrite b0 in b. done.
  intro. rewrite b0 in b. done.
  rewrite negbK. rewrite a0. simpl. 
  move=>_. move/andP. ssa. intro.
  move/negP. rewrite negb_and negb_or.
  move/orP. case. move/andP. case. intro. rewrite b.
  move=>_. move/andP. case. move/orP. case.
  intro. move/andP. case. intro. intro. rewrite b0 in b. done.
  intro. rewrite b0 in b. done.
  rewrite negb_and negbK. move/orP. case. intro. move/andP.
  case. move/orP. case. intro. move/andP.  rewrite a0. ssa.
  intro. rewrite b0 in b. done.
  move=>_. move/andP. case. move/orP. case. intro.
  move/andP. case. intro. intro. rewrite b0 in b. done.
  intro. rewrite b0 in b. done.
  rewrite !negb_and !negbK. move/orP. case.
  intro. 
  move/negP.
  rewrite !negb_and negbK.
  move/orP. case.
  move/orP. case. intro.
  move/negP. rewrite negb_and negb_or.
  move/orP. case.
  move/andP. case. intro. intro.
  move/andP. case.
  move/orP. case.
  intro. move/andP. case. intro. intro. rewrite b0 in b. done.
  intro. rewrite b0 in b. done.
  rewrite !negb_and negbK. move/orP. case.
  intro.
  move/andP. case. move/orP. case.
  intro. move/andP. case. rewrite a1. done.
  move=>->. rewrite a1. done.
  intro. move/andP. case.
  move/orP. case. intro. move/andP. case.
  rewrite a. done.
  intro. rewrite b0 in b. done.
  done. move/orP. case. intro.
  move/negP. rewrite negb_and negb_or.
  rewrite negb_and.
  move/orP. case. move/andP. case.
  intro. intro. move/andP. case.
  move/orP. case. intro. rewrite a. done.
  intro. rewrite b0 in b. done.
  rewrite negbK. move/orP. case. intro.
  move/andP. case. move/orP. case.
  intro. move/andP. case. intro. rewrite a in a3. done.
  move=>->. rewrite a. done.
  intro. move/andP. case.
  move/orP. case. intro.
  move/andP. case. intro. intro. rewrite b0 in b. done.
  intro. rewrite b0 in b. done.
  intro.
  move/negP. rewrite negb_and negb_or.
  move/orP. case. move/andP. case.
  intro. intro.
  move/andP. case. move/orP. case.
  intro. move/andP. case. intro.
  intro. rewrite b1 in b0. done.
  intro. rewrite b1 in b0. done.
  rewrite !negb_and negbK. move/orP. case.
  intro. move/andP. case.
  move/orP. case. intro. move/andP. case.
  rewrite a0. done.
  intro. rewrite b0 in b. done.
  intro. move/andP. case. move/orP. case.
  intro. move/andP. case. intro.
  intro. rewrite b1 in b. done.
  intro. rewrite b1 in b. done.
  intro. 
  move/negP. rewrite negb_and negb_or.
  move/orP. case. move/andP. case. intro.
  intro.
  move/negP. rewrite !negb_and. move/orP. 
  rewrite negb_or.
  case. move/andP. case. intro.
  intro. move/andP. case. move/orP. case.
  intro. move/andP. case. intro. intro. rewrite b2 in b1. done.
  intro. rewrite b2 in b1. done.
  rewrite negbK. move/orP. case. intro.
  move/andP. case. move/orP. case. intro.
  move/andP. case. intro. intro. rewrite b1 in b. done.
  intro. rewrite b1 in b. move/andP. rewrite a0. ssa.
  intro.
  move/andP. case. move/orP. case.
  move=>b2. move/andP. case. intro. intro.
  rewrite b3 in b1. done.
  intro. rewrite b2 in b1. done.
  rewrite negb_and !negbK. move/orP. case.
  intro.
  move/negP. case.
  rewrite !negb_and negb_or.
  move/orP. case.
  move/andP. case. intro. intro. move/andP. case.
  move/orP. case. intro. rewrite a. ssa.
  intro. rewrite b1 in b0. done.
  rewrite negbK. rewrite a. ssa.
  intro.
  move/negP. rewrite negb_and negb_or.
  move/orP. case. move/andP. case.
  intro. intro. move/andP. case.
  move/orP. case. intro.
  move/andP. case. intro. intro. rewrite b2 in b1. done.
  intro. rewrite b2 in b1. done.
  rewrite negb_and negbK. move/orP. case.
  intro. move/andP. case. move/orP.
  case. intro. move/andP. case. rewrite a. done.
  intro. rewrite b1 in b. done.
  intro. move/andP. case.
  move/orP. case. intro. move/andP. case.
  intro. intro. rewrite b2 in b. done.
  intro. rewrite b2 in b. done.

  move=>[]HreadyD'[]HreadyDef' Hfirst'.
  rewrite Hfirst Hfirst'.

  clear Hready Hready' HreadyD HreadyDef Hfirst HreadyD' HreadyDef' Hfirst'.

  have: is_handler_pid (bool_coding v) = is_handler_pid (bool_coding v').
  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H0.
  case/rel_eqpair. rewrite !pair_rewr.
  move=>+ /publicRel_eq ->.

  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_. ssa.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->. ssa.
  move=>->.
  destruct (is_handler_pid _).
  have: get_re_sch (bool_coding v) = get_re_sch (bool_coding v').
  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.
  move/rel_eqpair : H0. case. rewrite !pair_rewr.

  move=>+ /publicRel_eq ->.
  move/publicRel_eq : H1=>->.

  move/eqsum_split.
  case.
  move=>[]i0'[]i1'[]->[]->_. ssa.
  move=>[]i0'[]i1'[]->[]->/publicRel_eq ->. ssa.

  move=>->.
  destruct (get_re_sch (bool_coding v')).

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.  

  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. rewrite !pair_rewr. done. done.
  apply/rel_eqpair2. con. done.
  apply/rel_eqpair2. con. done.
  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con.  eauto. rewrite !pair_rewr.

  move/publicRel_eq : H4=>->.
  move/rel_eqpair2 : H5.
  case. rewrite !pair_rewr. move=>_ /publicRel_eq ->//.
  move/publicRel_eq :H2=>->. done.
  apply/rel_eqpair2. con.
  apply/rel_eqpair2. con. done. 
  move/publicRel_eq : H2=>->. rewrite !pair_rewr.
  move/rel_eqpair2 : H5. case. rewrite !pair_rewr. move=>_ /publicRel_eq ->. ssa.
  apply/rel_eqpair2. con. rewrite !pair_rewr.
  move/rel_eqpair2 : H6. case. rewrite !pair_rewr.
  move/publicRel_eq ->. done.
  rewrite !pair_rewr.
  move/rel_eqpair2 : H6. case. rewrite !pair_rewr.
  move=>/publicRel_eq -> /publicRel_eq ->//.
  move/publicRel_eq : H2=>->//.


  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.    

  move/rel_eqpair : H0. case. rewrite !pair_rewr.
  move=>_ /publicRel_eq ->.
  move/publicRel_eq : H1=>->.
  move/publicRel_eq : H2=>->.
  move/publicRel_eq : H4=>->.  ssa.
  rewrite /odflt /oapp /get_prev_pid /get_prev_pid_wrap /get_prev_pid /get_pids !pair_rewr.
  destruct prev'. done.
  destruct scheduler_pid. auto. done.
  subst. cbv. case_if. done.
  destruct ir_count'. done. done.
  subst. ssa. subst. done. subst. done.

  
  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.    

  ssa. subst. done.
  subst. cbv. case_if. done.
  destruct ir_count'. done. done. subst. done. subst. done.
  subst. done.


  
  apply f_EP_comp.

  rewrite /step0.
  mrw. intro.
  intro. destruct i.
  intro. have: dis in_rel l i. ssa. clear H=>H.
  intros.
  rewrite /step_left.
  simpl in H. rewrite /ir_dis in H. destruct H. subst.

  move: v => [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa. de cur.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa.
  apply/rel_eqpair2. con. rewrite !pair_rewr. ssa. ssa.
  ssa.

  apply f_EP_comp.
  rewrite /step1.
  mrw. intros.
  destruct i. have: (step_right check_scheduler (inl i) v) = v. done. move=>->//.
  ssa.

  apply f_EP_comp.
  mrw. intros.
  destruct i. have: (step_right sliced_preroutine (inl i) v) = v. done. move=>->//.
  ssa.

  mrw. intros.
  destruct i.
  have:  (step_right (fun=> initiate_next bool_coding) (inl i) v) = v. done.
  move=>->. auto.
  ssa.

  (*map*)
  eapply map_NI.
  instantiate (1:= eqmaybe_false (eqpair (eqsum (privateRel Bool) (publicRel _)) (eqmaybe_false (privateRel _)))).
  mrw. intros.
  destruct i. destruct i'.
  rewrite !pair_rewr.
  apply rel_eqpair_R2' in H.
  destruct H. destruct H.
  remember H0. clear Heqr.
  move/eqsum_split : H0. case.
  move=>[]x0[]x1[]->[]->. auto.
  move=>[]x0[]x1[]->[]->Hout.
  apply rel_eqmaybe_false2.
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
  move/rel_eqmaybe_top. case.
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

  mrw. intros. 
  apply rel_eqsum_L2. eapply H.  
  
  eapply maybe_NI.
  eapply par_NI.
  eapply map_NI.
  instantiate (1:= eqpair_LR falseRel (_)).
  mrw. intros. apply rel_eqpair in H. destruct H.
  apply rel_eqpair_LR2. con. 2:eauto.
  clear H0.
  case/eqsum_split:H.
  move=>[]x[]y[]->[]->. intros.
  simpl in b. destruct b. destruct H. subst. eauto.
  subst. simpl. case_if. case_if. done. done.
  case_if. done. done.
  move=>[]x[]y[]->[]->/publicRel_eq->/=. done.
  mrw. intros. ssa.
  instantiate (1:= eqmaybe_swi (publicRel _) falseRel).
  mrw. intros. apply rel_eqmaybe_swi2 in H.
  destruct H. destruct H. destruct H. destruct H. destruct H0.
  subst. apply rel_eqmaybe. eauto.
  destruct H. destruct H. subst. auto.
  destruct H. destruct i. ssa. destruct i'. ssa. auto.

  apply swi_NI.
  intros. left. intro. intros.
  simpl in H. subst. ssa. intro. ssa.
  
  eapply maybe_NI. eapply map_NI. eauto. eauto.
  mrw. intros. apply rel_eqpair_LR2. con. auto. eauto.
  apply p_pub_NI.
  

  apply par_NI.
  (*map*)

  eapply map_NI.
  instantiate (1:= eqpair_LR falseRel _).
  mrw. intros. apply rel_eqpair in H. destruct H.
  apply rel_eqpair_LR2. con. 
  clear H0.
  case/eqsum_split:H.
  move=>[]x[]y[]->[]->. intros.
  simpl in b. destruct b. destruct H. subst. eauto.
  subst. simpl. case_if. case_if. done. done.
  case_if. done. done.
  move=>[]x[]y[]->[]->/publicRel_eq->/=. done. eauto.
  mrw. intros. ssa.
  instantiate (1:= eqmaybe_swi (privateRel _) falseRel).
  mrw. intros. apply rel_eqmaybe_swi2 in H.
  destruct H. destruct H. destruct H. destruct H. destruct H0.
  subst. apply rel_eqmaybe. eauto.
  destruct H. destruct H. subst. auto.
  destruct H. destruct i. ssa. destruct i'. ssa. ssa. intro. apply H0. intro. ssa. subst.
  intro. ssa. de i'. intro. apply H. intro. ssa. intro. apply H. intro. intros. subst.
  ssa. 

  apply swi_NI.
  intros. left. intro. intros.
  simpl in H. subst. ssa. intro. ssa.
  
  eapply maybe_NI. eapply map_NI. eauto. eauto.
  mrw. intros. apply rel_eqpair_LR2. con. auto. eauto.

  apply p_priv_NI.
  
  apply par_NI.
  (*map*)

  eapply map_NI.
  instantiate (1:= eqpair_LR falseRel _).
  mrw. intros. apply rel_eqpair in H. destruct H.
  apply rel_eqpair_LR2. con. 
  clear H0.
  case/eqsum_split:H.
  move=>[]x[]y[]->[]->. intros.
  simpl in b. destruct b. destruct H. subst. eauto.
  subst. simpl. case_if. case_if. done. done.
  case_if. done. done.
  move=>[]x[]y[]->[]->/publicRel_eq->/=. done. eauto.
  mrw. intros. ssa.
  instantiate (1:= eqmaybe_swi (publicRel _) falseRel).
  mrw. intros. apply rel_eqmaybe_swi2 in H.
  destruct H. destruct H. destruct H. destruct H. destruct H0.
  subst. apply rel_eqmaybe. eauto.
  destruct H. destruct H. subst. auto.
  destruct H. destruct i. ssa. destruct i'. ssa. ssa.
  
  apply swi_NI.
  intros. left. intro. intros.
  simpl in H. subst. ssa. intro. ssa.
  
  eapply maybe_NI. eapply map_NI. eauto. eauto.
  mrw. intros. apply rel_eqpair_LR2. con. auto. eauto.

  apply p_sched_NI.

  apply par_NI.
  (*map*)

  eapply map_NI.
  instantiate (1:= eqpair_LR (privateRel _) _).
  mrw. intros. apply rel_eqpair in H. destruct H.
  apply rel_eqpair_LR2. con. 
  clear H0.
  case/eqsum_split:H.
  move=>[]x[]y[]->[]->. intros.
  simpl in b. destruct b. destruct H. subst. eauto. eauto.
  move=>[]x[]y[]->[]->/publicRel_eq->/=.
  destruct (eqVneq l \bot). auto. left. ssa. intro. apply/negP. apply i0. apply/eqP. done.
  instantiate (1:= eqmaybe_false (privateRel _)). auto.
  mrw. intros. ssa.
  instantiate (1:= eqmaybe_swi (privateRel _) (privateRel _)).
  mrw. intros. apply rel_eqmaybe_swi2 in H.
  destruct H. destruct H. destruct H. destruct H. destruct H0.
  subst. apply rel_eqmaybe. eauto.
  destruct H. destruct H. subst. auto.
  destruct H. destruct i. ssa. destruct i'. ssa. ssa. de i'.
  
  apply swi_NI.
  intros.
  destruct (eqVneq l \bot). subst. right.
  intro. intros.
  elim: H. intros. con.
  intros. econ. done.
  intros. econ. 2:done. ssa.
  left. intro. intros.
  move/private_not_bot' : H=>->//. ssa.
  intro. subst. rewrite eqxx in i. done.
  intro. subst. rewrite eqxx in i. done.

  apply maybe_NI.
  eapply map_NI. eauto. eauto.

  mrw. intros. apply rel_eqpair_LR2. con. auto. eauto.

  eapply map_NI. eauto. eauto.
  mrw. intros.
  move:H. instantiate (1:=eqpair (privateRel _) (publicRel _)).
  move/rel_eqpair. case=>HH _.
  simpl in HH. destruct HH. destruct H. rewrite H0.
  case_if. auto. auto. subst. auto.
  
  eapply sta_NI.
  mrw. intros. simpl in H0. destruct H0. ssa. subst. auto.
  mrw. intros. auto.
  mrw. intros. auto.
  apply out_NI.


  apply par_NI.
  (*map*)

  eapply map_NI.
  instantiate (1:= eqpair_LR (privateRel _) _).
  mrw. intros. apply rel_eqpair in H. destruct H.
  apply rel_eqpair_LR2. con. 
  clear H0.
  case/eqsum_split:H.
  move=>[]x[]y[]->[]->. intros.
  simpl in b. destruct b. destruct H. subst. eauto. eauto.
  move=>[]x[]y[]->[]->/publicRel_eq->/=.
  destruct (eqVneq l \bot). auto. left. ssa. intro. apply/negP. apply i0. apply/eqP. done.
  instantiate (1:= eqmaybe_false (privateRel _)). auto.
  mrw. intros. ssa.
  instantiate (1:= eqmaybe_swi (privateRel _) (privateRel _)).
  mrw. intros. apply rel_eqmaybe_swi2 in H.
  destruct H. destruct H. destruct H. destruct H. destruct H0.
  subst. apply rel_eqmaybe. eauto.
  destruct H. destruct H. subst. auto.
  destruct H. destruct i. ssa. destruct i'. ssa. ssa. de i'.
  
  apply swi_NI.
  intros.
  destruct (eqVneq l \bot). subst. right.
  intro. intros.
  elim: H. intros. con.
  intros. econ. done.
  intros. econ. 2:done. ssa.
  left. intro. intros.
  move/private_not_bot' : H=>->//. ssa.
  intro. subst. rewrite eqxx in i. done.
  intro. subst. rewrite eqxx in i. done.

  apply maybe_NI.
  eapply map_NI. eauto. eauto.

  mrw. intros. apply rel_eqpair_LR2. con. auto. eauto.

  eapply map_NI. eauto. eauto.
  mrw. intros.
  move:H. instantiate (1:=eqpair (privateRel _) (publicRel _)).
  move/rel_eqpair. case=>HH _.
  simpl in HH. destruct HH. destruct H. rewrite H0.
  case_if. auto. auto. subst. auto.
  
  eapply sta_NI.
  mrw. intros. simpl in H0. destruct H0. ssa. subst. auto.
  mrw. intros. auto.
  mrw. intros. auto.
  apply out_NI.

  eapply map_NI.
  instantiate (1:= eqpair_LR falseRel _).
  mrw. intros. apply rel_eqpair in H. destruct H.
  apply rel_eqpair_LR2. con. 
  clear H0.
  case/eqsum_split:H.
  move=>[]x[]y[]->[]->. intros.
  simpl in b. destruct b. destruct H. subst. eauto.
  subst. simpl. case_if. case_if. done. done.
  case_if. done. done.
  move=>[]x[]y[]->[]->/publicRel_eq->/=. done. eauto.
  mrw. intros. ssa.
  instantiate (1:= eqmaybe_swi (publicRel _) falseRel).
  mrw. intros. apply rel_eqmaybe_swi2 in H.
  destruct H. destruct H. destruct H. destruct H. destruct H0.
  subst. apply rel_eqmaybe. eauto.
  destruct H. destruct H. subst. auto.
  destruct H. destruct i. ssa. destruct i'. ssa. ssa.
  
  apply swi_NI.
  intros. left. intro. intros.
  simpl in H. subst. ssa. intro. ssa.
  
  eapply maybe_NI. eapply map_NI. eauto. eauto.
  mrw. intros. apply rel_eqpair_LR2. con. auto. eauto.

  eapply map_NI. eauto. eauto.
  instantiate (1:=eqpair _ _).
  mrw. move=> l i i' /rel_eqpair[] + _.
  instantiate (1:= publicRel _). move=>/publicRel_eq ->. ssa.
  eapply sta_NI.
  mrw. intros. move: H0.
  move/publicRel_eq=>->//.
  mrw. intros. eauto.
  mrw. intros. auto.
  apply out_NI.

  Unshelve. all: apply publicRel.
Qed.  


(* === Section 6 (payoff): the top result.  model_sliced_userview = map id
   parse_output model_sliced; NI is obtained from model_sliced_NI by output
   weakening through parse_output (out_rel-related outputs map to
   final_out_rel-related ones).  (docs/noninterference.md §6.) === *)
Lemma model_sliced_userview_NI : NI in_rel final_out_rel (model_sliced_userview p_pub p_priv p_sched).
Proof.
  eapply map_NI. eauto. eauto.
  2: apply model_sliced_NI.
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

End Parametric.


(* === The concrete system, recovered by instantiation. === *)
Corollary model_sliced_concrete_NI : NI in_rel out_rel model_sliced_concrete.
Proof.
  apply model_sliced_NI.
  apply low_p_NI. apply high_p_NI. apply scheduler_NI.
Qed.

Corollary model_sliced_userview_concrete_NI :
  NI in_rel final_out_rel model_sliced_userview_concrete.
Proof.
  apply model_sliced_userview_NI.
  apply low_p_NI. apply high_p_NI. apply scheduler_NI.
Qed.  
