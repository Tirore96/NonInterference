
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

Require Export NonInterference.theories.generic_model.

(* =================================================================
   One concrete system, shared by the instances in model_immediate.v,
   model_sliced.v and model_timer_unmasked.v, and the machinery for running a model on it: named events,
   trace tactics and the state along a run.
   ================================================================= *)

(* The concrete alphabets. *)
Notation T_outC := (T_out TPublicOutput TTypeSyscall).
Notation T_out_userviewC := (T_out_userview TPublicOutput TTypeSyscall).

(* === 1. A concrete system ===

   Nothing in generic_model.v names a user process, a scheduler or a handler
   length.  This section supplies one of each, so that the models can be run and
   their behaviour exhibited as traces.  The slice size is the sliced policy's
   own, in model_sliced.v. *)

(* p_pub_concrete = out GetRequest *)
Definition p_pub_concrete := @out Empty TPublicOutput GetRequest.


(* alternate x y z pred =
     map inl (fun o => if o is inr (true, _) then x else y)
       (loop (map id inr
         (sta (fun i v => if i is inl i' then v || pred i' else false)
              (fun o v => v) false
              (out z)))) *)
Definition alternate (A B C : Ty) (x y : [B]) (z : [C]) (pred : [A] -> bool) :=
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
(* p_priv_concrete = alternate Syscall NOP tt (fun i => i == Notify) *)
Definition p_priv_concrete := @alternate THandlerOutput TTypeSyscall Unit Syscall Idle tt (fun i => i == Notify).

(* scheduler =
     map id (fun o => o.1 + 2)
       (sta (fun _ v => v) (fun _ v => v.+1 %% 2) 1 (out tt)) *)
Definition scheduler : Proc Empty Nat :=
  map (O := Times Nat Unit) (O' := Nat) id
    (fun o => o.1 + 2)                        (*skip the interrupt handlers to reach p_priv_concrete and p_pub_concrete*)
    (sta (V := Nat) (O := Unit)
       (fun _ v => v) (fun _ v => v.+1 %% 2)
       1                                      (*will start scheduling the high process*)
       (out (O := Unit) tt)).

(* The concrete handler length: handlers are two output steps long. *)
Definition handler_runtime := 2.

Definition slot_procs_concrete := slot_procs handler_runtime p_pub_concrete p_priv_concrete scheduler.
Definition pool_concrete := pool handler_runtime p_pub_concrete p_priv_concrete scheduler.

(* === 2. Example traces ===

   Each model is exercised on two runs of the concrete system, on the same input
   schedule: one with no disk interrupt and one with a disk interrupt.  Reading
   the two [model_immediate] traces against each other shows the leak -- the
   public process loses output steps to the handler -- and the two
   [model_sliced] traces show that it is gone.  The [model_sliced_userview]
   traces are the [model_sliced] ones under [parse_output]. *)

(* -- Named inputs and outputs -- *)
Definition Tsum' := ([T_in] + [T_outC])%type.
Definition Tsum := Sum T_in T_out_userviewC.

Definition dI' : Tsum' := inl (inl tt).
Definition tI' : Tsum' := inl (inr tt).
Definition low_out x : [T_outC] := (Some x,(None,(None,(None,(None,None))))).
Definition high_out x : [T_outC] := (None,(Some x,(None,(None,(None,None))))).
Definition sched_o x : [T_outC] := (None,(None,(Some x,(None,(None,None))))).
Definition nop_o x : [T_outC] := (None,(None,(None,(Some x,(None,None))))).
Definition dI_o x : [T_outC] := (None,(None,(None,(None,(Some x,None))))).
Definition tI_o x : [T_outC] := (None,(None,(None,(None,(None,Some x))))).

Definition tmr_done' : Tsum' :=  inr (tI_o (Notify)).
Definition tmr_step' : Tsum' :=  inr (tI_o (Nothing)).

Definition dsk_done' : Tsum' :=  inr (dI_o (Notify)).
Definition dsk_step' : Tsum' :=  inr (dI_o (Nothing)).

Definition out_get' : Tsum' := inr (low_out GetRequest).
Definition out_nop' : Tsum' := inr (high_out Idle).
Definition out_syscall' : Tsum' := inr (high_out Syscall).

Definition sched_pub' : Tsum' := inr (sched_o 3).
Definition sched_priv' : Tsum' := inr (sched_o 2).

Definition nop_step' : Tsum' :=  inr (nop_o (Nothing)).
Definition nop_done' : Tsum' :=  inr (nop_o (Notify)).

Definition out_get : [Tsum] := inr (Some (inl (GetRequest))).
Definition out_nop : [Tsum] := inr (Some (inr Idle)).
Definition out_syscall : [Tsum] := inr (Some (inr Syscall)).
Definition w_None : [Tsum] := inr None.
Definition tI : [Tsum] := inl (inr tt).
Definition dI : [Tsum] := inl (inl tt).

Definition seqtype' := seq Tsum'.
Definition seqtype := seq ([T_in] + [T_out_userviewC]).


(* -- the four runs --

   All four share one input schedule: the disk interrupt (if any) after step 1,
   the timer interrupt after step 3; each has twelve output steps.  Without the
   disk interrupt the two policies behave alike.  With it, model_immediate hands
   steps 3-4 to the disk handler, taking them from the public process, while
   model_sliced records the interrupt as pending and runs the disk handler in
   place of the first NOP run of the slice.  Each "with" run minus its [dI'] is
   the matching "no" run, so each pair is an instance of the deletion clause of
   NI. *)

(* Unfolds everything below the policy; a proof about a policy's concrete model
   first unfolds the model itself. *)
Ltac rewr := rewrite /model /reactive_system /pool_concrete /pool /process_pool /slot_initial /p_pub_concrete /alternate /p_priv_concrete /pool_input /tI_o /ir_handler /f_proj /scheduler /low_out /pool_concrete /pool /pool_input /f_proj.

Ltac lsolv := try solve [ reduce_tac;reduce_tac | reduce_tac;try solve [reduce_once | econ];simpl;first (reduce_tac;reduce_tac)];simpl.
Ltac reduce_tac2 :=
  (try rewr);
   (repeat
      reduce_once);(try swi_instans); rewrite ?eqxx /= /xor /=.

Ltac sta_state_reduce :=
  match goal with
  | |- context [(@sta (Sum T_in T_outC) T_outC state_type _ (output_update _ _) ?state _)] =>let reduced := eval cbv in state in
                                                                                                          pattern state; match goal with |- ?F state => change (F reduced) end; cbv beta
  end.

Ltac trace_step := (first [econ;[idtac | econ | idtac] | econ];
  reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).
(* the last element is proved by hand, to avoid evar holes in the proof *)
Ltac trace_last := (first [econ;[idtac | econ | idtac] | econ];
  reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans);
  econ; reduce_tac2;reduce_tac2; econ; econ; reduce_tac; econ; econ;
  reduce_tac; econ; econ; reduce_tac; econ; econ; reduce_tac; econ;
  econ; reduce_tac; econ; econ; reduce_tac; econ.

(* -- The state along the four runs (Paper, Figs. 4 and 7, lower rows) --

   [run_states] gives the state after each event of a run, from the policy's
   initial state; [run_states_model] below shows these are the states the model
   holds along that run.  [state_row] keeps
   the slice counter, the timer and disk masks, and the disk and NOP pending
   bits.  Under [model_immediate] the masks differ between the two runs: the
   disk handler holds them set at steps 3-4, and the masks are public.  Under
   [model_sliced] the counter and the masks agree; the runs differ only in the
   private pending bits, and from the second run of the slice on not at all. *)
Definition run_states (init : [state_type])
  (observe : [T_outC] -> [state_type] -> [state_type])
  (advance : [state_type] -> [state_type]) (es : seqtype') :=
  scanl (fun v e => state_step observe advance e v) init es.
Definition state_row (v : [state_type]) :=
  (get_slice_count v, get_ir_mask v timer_irq, get_ir_mask v disk_irq,
   get_ir_pending v disk_irq, get_ir_pending v nop_irq).

(* -- The state rows are the model's own states --

   [state_step] is a function on states, and the model holds its state inside a
   [sta].  [system v q] is the model with state [v] and pool [q]; reduction stays
   in this form, and moves the state by exactly [state_step].  So the n-th entry
   of [run_states es] is the state the model holds after the first n+1 events of
   [es], for any [es] that is a trace of the model at [public_equiv], such as the
   four runs ([trace_immediate_no_dI'] and the others, in the policy files). *)
Inductive Steps (I O : Ty) : seq ([I] + [O]) -> Proc I O -> Proc I O -> Prop :=
| Steps0 p : Steps nil p p
| StepsI p i p' t p'' : reduceI p i p' -> Steps t p' p'' -> Steps (inl i :: t) p p''
| StepsO p o p' t p'' : reduceO p o p' -> Steps t p' p'' -> Steps (inr o :: t) p p''.

Lemma Trace_Steps l (es : seqtype') (p : Proc T_in T_outC) n :
  Trace (public_equiv _) l es p -> exists p', Steps (take n es) p p'.
Proof.
move=> H; elim: H n => [p0|p0 i p1 t Hr _ IH|p0 o' o p1 t Hr Ho _ IH] [|n] /=;
  try by exists p0; constructor.
- by case: (IH n) => p' Hs; exists p'; econstructor; eauto.
- by move: Ho => /= Ho; subst; case: (IH n) => p' Hs; exists p'; econstructor; eauto.
Qed.

Section ModelStates.
Variables (observe : [T_outC] -> [state_type] -> [state_type])
          (advance : [state_type] -> [state_type]).

Definition system (v : [state_type]) (q : Proc (Times cur_pid T_intermediate) T_outC) : Proc T_in T_outC :=
  @reactive_system cur_pid state_type v T_in T_outC T_intermediate
    (@input_update _ _) (output_update observe advance) (no_output _ _) q (@pool_input _ _).

Lemma system_stepI v q i p :
  reduceI (system v q) i p -> exists q', p = system (state_step observe advance (inl i) v) q'.
Proof. by move/reduceI_fun => ->; exists q. Qed.

Lemma system_stepO v q o p :
  reduceO (system v q) o p -> exists q', p = system (state_step observe advance (inr o) v) q'.
Proof.
move/reduceO_fun; rewrite /system /reactive_system /=.
case: (stepO q) => o0 q0 /= [-> ->].
by eexists.
Qed.

Lemma system_steps (es : seqtype') v q p :
  Steps es (system v q) p ->
  exists q', p = system (foldl (fun v e => state_step observe advance e v) v es) q'.
Proof.
elim: es v q p => [|[i|o] es IH] v q p H; inversion H; subst; clear H.
- by exists q.
- match goal with Hr : reduceI _ _ _, Hs : Steps _ _ _ |- _ =>
    case: (system_stepI Hr) => q' E; subst; exact: (IH _ _ _ Hs) end.
- match goal with Hr : reduceO _ _ _, Hs : Steps _ _ _ |- _ =>
    case: (system_stepO Hr) => q' E; subst; exact: (IH _ _ _ Hs) end.
Qed.

Theorem run_states_model init q l (es : seqtype') n :
  Trace (public_equiv _) l es (system init q) -> n < size es ->
  exists q', Steps (take n.+1 es) (system init q)
                   (system (nth init (run_states init observe advance es) n) q').
Proof.
move=> Ht Hn; case: (Trace_Steps n.+1 Ht) => p Hs.
case: (system_steps Hs) => q' E; exists q'.
by rewrite /run_states nth_scanl // -E.
Qed.

End ModelStates.

Definition map_tr (I O O' : Ty) (f : [O] -> [O']) (s : seq ([I] + [O])) := seq.map (fun x => match x with | inl x' => inl x' | inr y => inr (f y) end) s.
Lemma Trace_map : forall (A B B' : Ty) (p : Proc A B) (f : [B] -> [B']) (s : seq ([A] + [B])) (BRel : cEquiv [B]) (BRel' : cEquiv [B']) l,
    f_NI BRel BRel' f ->
    Trace BRel l s p -> Trace BRel' l (map_tr f s) (map id f p).
Proof.
  intros.
  elim : H0;ssa.
  econ. econ. econ. eauto. done.
  econ. econ. econ. eauto. apply H. done. done.
Qed.

