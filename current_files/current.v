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
                                      | 3 => Times Nat Bool
                                      | _ => Unit
                                      end.
Definition my_T_in := Sum Unit TInterrupt. (*We need Unit input to be able to differentiate trace, otherwise we only have interrupts in the trace*)
Definition my_T_out := Option (Sum TPublicOutput TTypeSyscall).
Definition my_T_in' := Times Nat (times_Option_n 3 my_f_I).
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

(* V_inner represents the internal state of the scheduler. It is structured as:
   ((curr, tm), dk) : (bool * bool) * bool
   - curr (bool): The currently scheduled user process.
                  'false' corresponds to process 2 (high_p)
                  'true' corresponds to process 3 (low_p)
   - tm (bool):   Timer interrupt pending register. If true, the scheduler needs to run
                  in cooperative preemption mode.
   - dk (bool):   Disk interrupt pending register. Tracks if a disk interrupt is active
                  and pending CPU attention. *)
Definition V_inner := Times (Times Bool Bool) Bool.

(* get_state_and_timer is a helper process of type Proc (Times V_inner TInterrupt) (Times V_inner Bool).
   It assists the scheduler's state transitions by pre-processing the incoming interrupt.
   - Input: The scheduler state and the incoming TInterrupt (TimerInterrupt or DiskInterrupt).
   - Output: The scheduler state paired with a boolean 'is_timer' which is 'true' if the
     incoming interrupt is TimerInterrupt, and 'false' if it is DiskInterrupt.
   This avoids the need for complex, nested pattern matches inside the state transition function
   and makes the scheduler's outer output mapping much simpler. *)
Definition get_state_and_timer : Proc (Times V_inner TInterrupt) (Times V_inner Bool) :=
  @map (Times V_inner TInterrupt) (Times V_inner TInterrupt) (Times (Times V_inner Bool) Unit) (Times V_inner Bool)
    id (fun x => fst x)
    (@sta (Times V_inner TInterrupt) Unit (Times V_inner Bool)
         (fun x v => (fst x, match snd x with | TimerInterrupt => true | DiskInterrupt => false end))
         (fun _ v => v)
         (((false, false), false), false)
         (@out (Times (Times V_inner Bool) (Times V_inner TInterrupt)) Unit tt)).

(* bad_schedulerp represents the preemptive scheduler (analogous to standard Linux-like preemptive OS).
   - Input: TInterrupt (Timer or Disk interrupt).
   - Output: (next_proc, handle_disk) : Nat * Bool
     - next_proc (nat): The process scheduled for the next CPU step.
     - handle_disk (bool): Disk preemption flag. If true, disk interrupts immediately preempt.
   
   Behavior:
   1. Output Mapping:
      - If 'is_timer' is true, immediately schedule the handler (index 1) and enable disk preemption (1, true).
      - If 'tm' (pending timer) is true, execute cooperative round-robin scheduling (schedule next_proc, enable disk preemption).
      - Else, continue running the currently scheduled process (schedule curr, enable disk preemption).
   2. State Transition (sta):
      - Upon receiving an interrupt 'ih':
        - TimerInterrupt sets 'tm' (pending timer) to true.
        - DiskInterrupt sets 'dk' (pending disk) to true.
      - Upon loop feedback:
        - If 'is_timer' is true, the state remains unchanged.
        - Otherwise, update 'curr' to 'p_next == 3' and clear 'tm' (as it is now handled). *)
Definition bad_schedulerp : Proc TInterrupt (Times Nat Bool) :=
  @map TInterrupt TInterrupt (Times V_inner (Times V_inner Bool)) (Times Nat Bool)
    id (fun o => 
      let '(((curr, tm), dk), is_timer) := snd o in
      if is_timer then (1, true)
      else if tm then (if curr then 2 else 3, true)
      else (if curr then 3 else 2, true))
    (@sta TInterrupt (Times V_inner Bool) V_inner
         (fun ih '((curr, tm), dk) => 
            match ih with 
            | TimerInterrupt => ((curr, true), dk) 
            | DiskInterrupt => ((curr, tm), true)
            end)
         (fun o '((curr, tm), dk) => 
            let '(((curr', tm'), dk'), is_timer) := o in
            if is_timer then
              ((curr', tm'), dk')
            else
              let p_next := if tm' then (if curr' then 2 else 3) else (if curr' then 3 else 2) in
              ((p_next == 3, false), dk'))
         ((false, false), false)
         get_state_and_timer).

(* good_schedulerp represents the mitigated scheduler.
   - Input: TInterrupt (Timer or Disk interrupt).
   - Output: (next_proc, handle_disk) : Nat * Bool
     - next_proc (nat): The process scheduled for the next CPU step.
     - handle_disk (bool): Disk preemption flag. Always 'false', meaning disk interrupts
       cannot immediately preempt the executing process.
   
   Behavior:
   1. Output Mapping:
      - Same scheduling logic as the bad scheduler, but the disk preemption flag 'handle_disk'
        is always set to 'false'. This mitigates potential timing side-channels from immediate
        preemption.
   2. State Transition (sta):
      - Upon receiving an interrupt 'ih':
        - TimerInterrupt sets 'tm' (pending timer) to true.
        - DiskInterrupt is ignored (the pending disk flag 'dk' remains unchanged).
      - Upon loop feedback:
        - Same state update logic as the bad scheduler. *)
Definition good_schedulerp : Proc TInterrupt (Times Nat Bool) :=
  @map TInterrupt TInterrupt (Times V_inner (Times V_inner Bool)) (Times Nat Bool)
    id (fun o => 
      let '(((curr, tm), dk), is_timer) := snd o in
      if is_timer then (1, false)
      else if tm then (if curr then 2 else 3, false)
      else (if curr then 3 else 2, false))
    (@sta TInterrupt (Times V_inner Bool) V_inner
         (fun ih '((curr, tm), dk) => 
            match ih with 
            | TimerInterrupt => ((curr, true), dk) 
            | DiskInterrupt => ((curr, tm), dk)
            end)
         (fun o '((curr, tm), dk) => 
            let '(((curr', tm'), dk'), is_timer) := o in
            if is_timer then
              ((curr', tm'), dk')
            else
              let p_next := if tm' then (if curr' then 2 else 3) else (if curr' then 3 else 2) in
              ((p_next == 3, false), dk'))
         ((false, false), false)
         get_state_and_timer).

Definition unit_p : Proc Unit Unit := @out Unit Unit tt.

Definition my_procs_good (n : nat) : Proc (my_f_I n) (my_f_O n).
Proof. by case: n => [| [| [| [| n]]]]; [apply: handler | apply: high_p | apply: low_p | apply: good_schedulerp | apply: unit_p]. Defined.

Definition my_procs_bad (n : nat) : Proc (my_f_I n) (my_f_O n).
Proof. by case: n => [| [| [| [| n]]]]; [apply: handler | apply: high_p | apply: low_p | apply: bad_schedulerp | apply: unit_p]. Defined.

Definition my_f_coopt n := n == 4.
Definition my_f_initial (n : nat) := false.
Definition process_pool_good := @scheduled_process_pool 3 my_f_coopt my_f_initial my_f_I my_f_O my_procs_good.
Definition process_pool_bad := @scheduled_process_pool 3 my_f_coopt my_f_initial my_f_I my_f_O my_procs_bad.

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
  let '(sch, (low, (high, handl))) := t in
  match sch, handl with
  | Some s, _ => (fst s, none4)
  | None, Some h => (4, (None, (None, (Some h, None))))
  | None, None => (0, none4)
  end.
Definition my_f_in_sch_good (t : [my_T_in]) : nat := match t with | inl tt | inr DiskInterrupt => 0 | inr TimerInterrupt => 0 end.
Definition my_f_in_t (t : [my_T_in]) : [times_Option_n 3 my_f_I] :=
  match t with
  | inl tt => (None, (Some tt, (None, None)))
  | inr TimerInterrupt => (Some TimerInterrupt, (None, (None, None)))
  | inr DiskInterrupt => (None, (None, (None, Some DiskInterrupt)))
  end.
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
      and whether the interrupt handler is currently active.
   4. disk_preempt_enabled            : Set by the scheduler to control whether disk interrupts
      preempt immediately. *)
Definition V_state := Times (Times (Times Bool Bool) (Times Bool Bool)) (Times (Times Nat Bool) Bool).

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
  let p_sched        := fst (fst (snd v)) in
  let handler_active := snd (fst (snd v)) in
  let disk_preempt_enabled := snd (snd v) in
  
  match fst o with
  | Some (p_next, handle_disk) =>
      (* Scheduler ran! *)
      let timer_pending' := false in
      let timer_received' := false in
      let p_sched' := p_next in
      let disk_preempt_enabled' := handle_disk in
      let handler_active' := disk_pending && handle_disk in
      let disk_pending' := if disk_pending && handle_disk then false else disk_pending in
      let disk_received' := if disk_pending && handle_disk then false else disk_received in
      ((timer_received', disk_received'), (timer_pending', disk_pending'), ((p_sched', handler_active'), disk_preempt_enabled'))
  | None =>
      match snd (snd (snd o)) with
      | Some _ =>
          (* Handler ran! *)
          let handler_active' := false in
          let disk_pending' := false in
          let disk_received' := false in
          ((timer_received, disk_received'), (timer_pending, disk_pending'), ((p_sched, handler_active'), disk_preempt_enabled))
      | None =>
          (* Normal process ran! *)
          let timer_pending' := if timer_received then true else timer_pending in
          let disk_pending'  := if disk_received then true else disk_pending in
          let timer_received' := false in
          let disk_received'  := false in
          let handler_active' := if disk_preempt_enabled && (disk_received || disk_pending) then true else handler_active in
          let disk_pending'' := if disk_preempt_enabled && (disk_received || disk_pending) then false else disk_pending' in
          let disk_received'' := if disk_preempt_enabled && (disk_received || disk_pending) then false else disk_received' in
          ((timer_received', disk_received''), (timer_pending', disk_pending''), ((p_sched, handler_active'), disk_preempt_enabled))
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
  let p_sched        := fst (fst (snd v)) in
  let handler_active := snd (fst (snd v)) in
  
  if timer_pending then
    ((p_sched, 4), (Some TimerInterrupt, (None, (None, None))))
  else if handler_active then
    ((0, 1), (None, (None, (None, Some DiskInterrupt))))
  else
    let routed_sch := fst i_in' in
    let final_sch := if routed_sch == 0 then (p_sched, p_sched)
                     else if routed_sch == 4 then (1, 4)
                     else (p_sched, routed_sch) in
    let final_pool_input := if routed_sch == 4 then
                              (Some DiskInterrupt, (None, (fst (snd (snd i_pool)), None)))
                            else if p_sched == 1 then
                              (None, (None, (None, if disk_pending then Some DiskInterrupt else None)))
                            else
                              clear_interrupts i_pool in
    (final_sch, final_pool_input).

Definition v_state_init : [V_state] :=
  ((false, false), (false, false), ((2, false), false)).

Definition my_only_loop_good_inner : Proc my_T_in' my_T_out' :=
  @map my_T_in' my_T_in' (Times V_state my_T_out') my_T_out' id (fun x => snd x)
    (sta f_state g_state v_state_init
      (@map (Times V_state my_T_in') (Times (Times Nat Nat) I_pool) my_T_out' my_T_out' override_pool_input id process_pool_good)).

Definition my_only_loop_good' := @only_loop my_T_in' my_T_out' my_f_route_good my_def my_only_loop_good_inner.

Definition my_only_loop_good : Proc my_T_in my_T_out :=
  @map my_T_in my_T_in' my_T_out' my_T_out my_f_in_good my_f_out my_only_loop_good'.

Definition my_only_loop_bad_inner : Proc my_T_in' my_T_out' :=
  @map my_T_in' my_T_in' (Times V_state my_T_out') my_T_out' id (fun x => snd x)
    (sta f_state g_state v_state_init
      (@map (Times V_state my_T_in') (Times (Times Nat Nat) I_pool) my_T_out' my_T_out' override_pool_input id process_pool_bad)).

Definition my_only_loop_bad' := @only_loop my_T_in' my_T_out' my_f_route_good my_def my_only_loop_bad_inner.

Definition my_only_loop_bad : Proc my_T_in my_T_out :=
  @map my_T_in my_T_in' my_T_out' my_T_out my_f_in_good my_f_out my_only_loop_bad'.

Definition out0 x : [my_T_out'] := (Some x,(None,(None,None))).
Definition out1 x : [my_T_out'] := (None,(Some x,(None,None))).
Definition out2 x : [my_T_out'] := (None,(None,(Some x,None))).
Definition out3 x : [my_T_out'] := (None,(None,(None, Some x))).

(*Spec for good scheduler*)
Definition seqtype' := seq ([my_T_in'] + [my_T_out']).
Definition newtrace' : seqtype' :=
  cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 1 *)
  (cons (inr (out2 NOP)) (* Step 2: high_p *)
  (cons (inr (out0 (1, false))) (* Step 3: scheduler *)
  (cons (inr (out3 Nothing)) (* Step 4: handler *)
  (cons (inr (out0 (3, false))) (* Step 5: scheduler *)
  (cons (inr (out1 GetRequest)) (* Step 6: low_p *)
  (cons (inl (my_f_in_good (inr DiskInterrupt))) (* Step 7 *)
  (cons (inr (out1 GetRequest)) (* Step 8: low_p *)
  (cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 9 *)
  (cons (inr (out1 GetRequest)) (* Step 10: low_p *)
  (cons (inr (out0 (1, false))) (* Step 11: scheduler *)
  (cons (inr (out3 Notify)) (* Step 12: handler *)
  (cons (inr (out0 (2, false))) (* Step 13: scheduler *)
  (cons (inr (out2 Syscall)) nil))))))))))))).

Definition seqtype := seq ([my_T_in] + [my_T_out]).

Definition newtrace_wrap : seqtype  :=
  cons (inl (inr TimerInterrupt)) (* Step 1 *)
  (cons (inr (Some (inr NOP))) (* Step 2 *)
  (cons (inr None) (* Step 3 *)
  (cons (inr None) (* Step 4 *)
  (cons (inr None) (* Step 5 *)
  (cons (inr (Some (inl GetRequest))) (* Step 6 *)
  (cons (inl (inr DiskInterrupt)) (* Step 7 *)
  (cons (inr (Some (inl GetRequest))) (* Step 8 *)
  (cons (inl (inr TimerInterrupt)) (* Step 9 *)
  (cons (inr (Some (inl GetRequest))) (* Step 10 *)
  (cons (inr None) (* Step 11 *)
  (cons (inr None) (* Step 12 *)
  (cons (inr None) (* Step 13 *)
  (cons (inr (Some (inr Syscall))) nil))))))))))))).

(*Spec for good scheduler without disk interrupt*)
Definition newtrace_no_disk : seqtype' :=
  cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 1 *)
  (cons (inr (out2 NOP)) (* Step 2: high_p *)
  (cons (inr (out0 (1, false))) (* Step 3: scheduler *)
  (cons (inr (out3 Nothing)) (* Step 4: handler *)
  (cons (inr (out0 (3, false))) (* Step 5: scheduler *)
  (cons (inr (out1 GetRequest)) (* Step 6: low_p *)
  (cons (inl (my_f_in_good (inl tt))) (* Step 7 *)
  (cons (inr (out1 GetRequest)) (* Step 8: low_p *)
  (cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 9 *)
  (cons (inr (out1 GetRequest)) (* Step 10: low_p *)
  (cons (inr (out0 (1, false))) (* Step 11: scheduler *)
  (cons (inr (out3 Nothing)) (* Step 12: handler *)
  (cons (inr (out0 (2, false))) (* Step 13: scheduler *)
  (cons (inr (out2 NOP)) nil))))))))))))).

Definition newtrace_no_disk_wrap : seqtype  :=
  cons (inl (inr TimerInterrupt)) (* Step 1 *)
  (cons (inr (Some (inr NOP))) (* Step 2 *)
  (cons (inr None) (* Step 3 *)
  (cons (inr None) (* Step 4 *)
  (cons (inr None) (* Step 5 *)
  (cons (inr (Some (inl GetRequest))) (* Step 6 *)
  (cons (inl (inl tt)) (* Step 7 *)
  (cons (inr (Some (inl GetRequest))) (* Step 8 *)
  (cons (inl (inr TimerInterrupt)) (* Step 9 *)
  (cons (inr (Some (inl GetRequest))) (* Step 10 *)
  (cons (inr None) (* Step 11 *)
  (cons (inr None) (* Step 12 *)
  (cons (inr None) (* Step 13 *)
  (cons (inr (Some (inr NOP))) nil))))))))))))).

Ltac model.rewr ::= rewrite /low_p /handler /high_p /my_only_loop_good' /my_only_loop_good /my_only_loop_good_inner /only_loop /process_pool_good /process_pool_bad /good_schedulerp /my_f_coopt /scheduled_process_pool /high_p /alternate_generic /alternate_generic2 /low_p /my_f_in_good /my_f_in_sch_good /my_f_in_t /get_state_and_timer /bad_schedulerp /my_procs_good /my_procs_bad /f_state /g_state /override_pool_input /clear_interrupts /v_state_init /my_only_loop_bad' /my_only_loop_bad /my_only_loop_bad_inner /=.

Ltac reduce_tac ::= try model.rewr; repeat reduce_once; try swi_instans; controlled_eauto; rewrite ?eqtype.eq_refl /= /xor /=; repeat (reduce_once || econ || reflexivity).

Lemma newtrace'_trace : Trace (eqpair_LR (eqmaybe (publicRel (Times Nat Bool)))
                          (eqpair_LR (eqmaybe (publicRel TPublicOutput))
                             (eqpair_LR (eqmaybe (semiprivateRel TTypeSyscall))
                                 (eqmaybe (semiprivateRel THandlerOutput))))) false newtrace' my_only_loop_good'.
Admitted.

Lemma newtrace_trace : Trace (eqmaybe (eqsum_LR (publicRel TPublicOutput) (semiprivateRel TTypeSyscall))) false newtrace_wrap my_only_loop_good.
Proof.
Admitted.

Lemma newtrace_no_disk_trace : Trace (eqpair_LR (eqmaybe (publicRel (Times Nat Bool)))
                          (eqpair_LR (eqmaybe (publicRel TPublicOutput))
                             (eqpair_LR (eqmaybe (semiprivateRel TTypeSyscall))
                                 (eqmaybe (semiprivateRel THandlerOutput))))) false newtrace_no_disk my_only_loop_good'.
Proof.
Admitted.

Lemma newtrace_no_disk_wrap_trace : Trace (eqmaybe (eqsum_LR (publicRel TPublicOutput) (semiprivateRel TTypeSyscall))) false newtrace_no_disk_wrap my_only_loop_good.
Proof.
Admitted.

Definition badtrace' : seqtype' :=
  cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 1 *)
  (cons (inr (out2 NOP)) (* Step 2 *)
  (cons (inr (out0 (1, true))) (* Step 3 *)
  (cons (inr (out3 Nothing)) (* Step 4 *)
  (cons (inr (out0 (3, true))) (* Step 5 *)
  (cons (inr (out1 GetRequest)) (* Step 6 *)
  (cons (inl (my_f_in_good (inr DiskInterrupt))) (* Step 7 *)
  (cons (inr (out1 GetRequest)) (* Step 8 *)
  (cons (inr (out3 Notify)) (* Step 9 *)
  (cons (inr (out0 (3, true))) (* Step 10 *)
  (cons (inl (my_f_in_good (inr TimerInterrupt))) (* Step 11 *)
  (cons (inr (Some (1, true), (Some GetRequest, (None, None)))) (* Step 12 *)
  (cons (inr (None, (Some GetRequest, (None, Some Notify)))) (* Step 13 *)
  (cons (inr (Some (2, true), (Some GetRequest, (None, None)))) (* Step 14 *)
  (cons (inr (None, (Some GetRequest, (Some Syscall, None)))) nil)))))))))))))) .

Definition badtrace_wrap : seqtype :=
  cons (inl (inr TimerInterrupt))
  (cons (inr (Some (inr NOP)))
  (cons (inr None)
  (cons (inr None)
  (cons (inr None)
  (cons (inr (Some (inl GetRequest)))
  (cons (inl (inr DiskInterrupt))
  (cons (inr (Some (inl GetRequest)))
  (cons (inr None)
  (cons (inr None)
  (cons (inl (inr TimerInterrupt))
  (cons (inr (Some (inl GetRequest)))
  (cons (inr None)
  (cons (inr (Some (inl GetRequest)))
  (cons (inr (Some (inr Syscall))) nil)))))))))))))) .

Lemma badtrace'_trace : Trace (eqpair_LR (eqmaybe (publicRel (Times Nat Bool)))
                          (eqpair_LR (eqmaybe (publicRel TPublicOutput))
                             (eqpair_LR (eqmaybe (semiprivateRel TTypeSyscall))
                                 (eqmaybe (semiprivateRel THandlerOutput))))) false badtrace' my_only_loop_bad'.
Admitted.

Lemma badtrace_trace : Trace (eqmaybe (eqsum_LR (publicRel TPublicOutput) (semiprivateRel TTypeSyscall))) false badtrace_wrap my_only_loop_bad.
Proof.
Admitted.
