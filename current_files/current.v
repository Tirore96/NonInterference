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

Require Import NonInterference.theorems.

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
                                      | 3 => TInterrupt (*scheduler*)
                                      | _ => Unit
                                      end.

Definition my_f_O := fun (n : nat) => match n with
                                      | 0 => THandlerOutput
                                      | 1 => TTypeSyscall
                                      | 2 => TPublicOutput
                                      | 3 => Nat
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
Definition good_schedulerp :  Proc TInterrupt Nat.
  eapply map. apply id. instantiate (1:= Times Bool Unit).
  exact (fun o => if fst o then 3 else 2).
  eapply (@sta _ _ Bool).
  - exact (fun ih b => match ih with | TimerInterrupt => ~~ b | DiskInterrupt => b end).
  - exact (fun _ b => b).
  - exact false.
  - eapply out. con.
Defined.

(* Definition sstream := Stream ([(Sum TInterrupt THandlerOutput)] + [(Times Nat Nat)]).

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
Qed. *)

(*Lemma schedulerp_trace : trace my_sstream good_schedulerp.
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
Qed.*)


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
  | (Some sch,_) => ((sch, sch),none4)
  | (_ ,(Some publ, _)) => ((0,0),none4)
  | (_ ,(None,(Some prv,_))) => ((0,0),none4)
  | (_ ,(None,(None,Some handl))) => ((1,4),(None,(None,(Some handl,None)))) (*(1,4) = turn off yourself, turn on scheduler*)
  | _ => ((0,0),none4)    
  end.
Definition my_f_in_sch_good (t : [my_T_in]) : [Times Nat Nat] := match t with | inl tt | inr DiskInterrupt => (0,0) | inr TimerInterrupt => (0,4) end.
Definition my_f_in_t (t : [my_T_in]) : [ (times_Option_n 3 my_f_I) ] := match t with
                                                                        | inl tt => (None,(Some tt,(None,None)))
                                                                        | inr TimerInterrupt => (Some TimerInterrupt,(None,(None,None)))
                                                                        | inr DiskInterrupt => (None,(None,(None,Some DiskInterrupt))) end.
Definition my_f_in_good (t : [my_T_in]) : [my_T_in'] := (my_f_in_sch_good t, my_f_in_t t).
Definition my_f_out (t : [my_T_out']) := match t with
                                         | (_,(Some p,(None,None))) => Some (inl p)
                                         | (_,(None,(Some sys,None))) => Some (inr sys)
                                         | _ => None
                                         end.

(* V_state represents the CPU/OS internal state registers, combining:
   1. (timer_received, disk_received) : Latch registers that record when an interrupt
      signal is active on the bus during the current step.
   2. (timer_pending, disk_pending)   : Checked at the end of the CPU cycle (on output)
      to trigger preemption/switching for the *next* step.
   3. (p_sched, handler_active)       : Tracks which process has been scheduled by the OS (single Nat),
      and whether the interrupt handler is currently active. *)
Definition V_state := Times (Times (Times Bool Bool) (Times Bool Bool)) (Times Nat Bool).

(* Filters out scheduler and handler interrupt inputs from the input tuple,
   preventing them from leaking or causing premature process activation during
   normal process execution steps. *)
Definition clear_interrupts (i : [times_Option_n 3 my_f_I]) : [times_Option_n 3 my_f_I] :=
  (None, (fst (snd i), (fst (snd (snd i)), None))).

(* f_state is the state transition function on INPUT (inl transition).
   It latches incoming interrupt signals (TimerInterrupt or DiskInterrupt)
   into the timer_received and disk_received registers. The currently executing
   process is unaffected and completes its step. *)
Definition f_state (i_in' : [my_T_in']) (v : [V_state]) : [V_state] :=
  let i_pool := snd i_in' in
  let timer_rec := if fst i_pool is Some TimerInterrupt then true else fst (fst (fst v)) in
  let disk_rec  := if snd (snd (snd i_pool)) is Some DiskInterrupt then true else snd (fst (fst v)) in
  ((timer_rec, disk_rec), snd (fst v), snd v).

(* g_state is the state transition function on OUTPUT (inr transition).
   It updates the CPU registers at the end of each CPU cycle (step boundary):
   - If the scheduler ran: it updates the next scheduled process (p_sched) to the single Nat,
     clears the timer pending/received flags, and turns on the handler_active flag
     if a disk interrupt is pending and requires handling.
   - If the handler ran: it clears handler_active and the disk pending/received flags.
   - If a normal process ran: it promotes latched interrupts (timer_received/disk_received)
     to pending flags (timer_pending/disk_pending) to trigger context switches next. *)
Definition g_state (o : [my_T_out']) (v : [V_state]) : [V_state] :=
  let timer_received := fst (fst (fst v)) in
  let disk_received  := snd (fst (fst v)) in
  let timer_pending  := fst (snd (fst v)) in
  let disk_pending   := snd (snd (fst v)) in
  let p_sched        := fst (snd v) in
  let handler_active := snd (snd v) in
  
  match fst o with
  | Some p_next =>
      (* Scheduler ran! *)
      let timer_pending' := false in
      let timer_received' := false in
      let p_sched' := p_next in
      let handler_active' := disk_pending in
      let disk_pending' := if disk_pending then false else disk_pending in
      let disk_received' := if disk_pending then false else disk_received in
      ((timer_received', disk_received'), (timer_pending', disk_pending'), (p_sched', handler_active'))
  | None =>
      match snd (snd (snd o)) with
      | Some _ =>
          (* Handler ran! *)
          let handler_active' := false in
          let disk_pending' := false in
          let disk_received' := false in
          ((timer_received, disk_received'), (timer_pending, disk_pending'), (p_sched, handler_active'))
      | None =>
          (* Normal process ran! *)
          let timer_pending' := if timer_received then true else timer_pending in
          let disk_pending'  := if disk_received then true else disk_pending in
          let timer_received' := false in
          let disk_received'  := false in
          ((timer_received', disk_received'), (timer_pending', disk_pending'), (p_sched, handler_active))
      end
  end.

Definition I_pool := times_Option_n 3 my_f_I.

(* override_pool_input maps the stateful registers to pool-level execution flags:
   - If timer_pending is set: we preempt the running process, activate the scheduler (index 4),
     and feed it the TimerInterrupt.
   - If handler_active is set: we preempt the running process, activate the handler (index 1),
     and feed it the DiskInterrupt.
   - Otherwise: the normal scheduled process (p_sched) is executed as (p_sched, p_sched), and
     interrupt inputs are cleared. *)
Definition override_pool_input (x : [Times V_state my_T_in']) : [Times (Times Nat Nat) I_pool] :=
  let v := fst x in
  let i_in' := snd x in
  let i_pool := snd i_in' in
  let timer_pending := fst (snd (fst v)) in
  let disk_pending  := snd (snd (fst v)) in
  let p_sched        := fst (snd v) in
  let handler_active := snd (snd v) in
  
  if timer_pending then
    ((0, 4), (Some TimerInterrupt, (None, (None, None))))
  else if handler_active then
    ((0, 1), (None, (None, (None, Some DiskInterrupt))))
  else
    ((p_sched, p_sched), clear_interrupts i_pool).

Definition v_state_init : [V_state] :=
  ((false, false), (false, false), (2, false)).

Definition my_only_loop_good_inner : Proc my_T_in' my_T_out'.
  eapply (@map my_T_in' my_T_in' (Times V_state my_T_out') my_T_out'). exact id. exact (fun x => snd x).
  eapply (@sta _ _ V_state).
  - exact f_state.
  - exact g_state.
  - exact v_state_init.
  - eapply map.
    + exact override_pool_input.
    + exact id.
    + exact process_pool_good.
Defined.

Definition my_only_loop_good' := @only_loop my_T_in' my_T_out' my_f_route_good my_def my_only_loop_good_inner.

Definition my_only_loop_good : Proc my_T_in my_T_out .
  eapply map. apply my_f_in_good. apply my_f_out. apply my_only_loop_good'.
Defined.

  

Definition out0 x : [my_T_out'] := (Some x,(None,(None,None))).
Definition out1 x : [my_T_out'] := (None,(Some x,(None,None))).
Definition out2 x : [my_T_out'] := (None,(None,(Some x,None))).
Definition out3 x : [my_T_out'] := (None,(None,(None, Some x))).

(*Spec for good scheduler*)
(*Add diskinterrupt*)
Definition seqtype' := seq ([my_T_in'] + [my_T_out']).
Definition newtrace' : seqtype' :=
  cons (inl (my_f_in_good (inr TimerInterrupt)))
  (cons (inr (None, (None, (Some NOP, None))))
  (cons (inr (out0 3))
  (cons (inr (out1 GetRequest))
  (cons (inl (my_f_in_good (inr DiskInterrupt)))
  (cons (inr (out1 GetRequest))
  (cons (inl (my_f_in_good (inr TimerInterrupt)))
  (cons (inr (out1 GetRequest))
  (cons (inr (out0 2))
  (cons (inr (out3 Notify))
  (cons (inr (out2 Syscall)) nil)))))))))).

Definition seqtype := seq ([my_T_in] + [my_T_out]).

Definition newtrace_wrap : seqtype  :=
  cons (inl (inr TimerInterrupt))
  (cons (inr (Some (inr NOP)))
  (cons (inr None)
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inr DiskInterrupt))
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inr TimerInterrupt))
  (cons (inr (Some (inl GetRequest)))
  (cons (inr None)
  (cons (inr None)
  (cons (inr (Some (inr Syscall))) nil)))))))))).

Ltac rewr ::= rewrite /low_p /handler /high_p /only_loop /my_only_loop_good' /my_only_loop_good /process_pool_good /good_schedulerp /my_f_coopt /scheduled_process_pool /high_p /alternate_generic /alternate_generic2 /low_p.

Lemma newtrace'_trace : Trace (eqpair_LR (eqmaybe (publicRel Nat))
                          (eqpair_LR (eqmaybe (publicRel TPublicOutput))
                             (eqpair_LR (eqmaybe (semiprivateRel TTypeSyscall))
                                (eqmaybe (semiprivateRel THandlerOutput))))) false newtrace' my_only_loop_good'.
Proof.
Admitted.

Lemma newtrace_trace : Trace (eqmaybe (eqsum_LR (publicRel TPublicOutput) (semiprivateRel TTypeSyscall))) false newtrace_wrap my_only_loop_good.
Proof.
Admitted.
