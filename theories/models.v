
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

Require Export NonInterference.theories.theorems.

(* This file defines the process-scheduling models studied in the paper: three
   processes over interrupt inputs, culminating in [wrapped_model_good], the
   model proved non-interfering in noninterference.v.  The type abbreviations
   below ([T_in], [T_out'], [T_out]) fix the input/output interfaces. *)

Fixpoint times_n n (f : nat -> Ty) : Ty :=
  let t := f n in
  match n with
  | 0 => t
  | S n' => Times t (times_n n' f)
  end.
Definition times_on (n : nat) (f : nat -> Ty) := times_n n (Option \o f).


Definition T_in := TInterrupt.
Definition T_out' := Times (Option TPublicOutput) (Times (Option TTypeSyscall) (Times (Option Nat) (times_on 2 (fun _ => THandlerOutput)))).
Definition T_out := Option (Sum TPublicOutput TTypeSyscall).

(* =================================================================
   The three models (real Coq names, defined in sections 7-9 below):

     model_bad          : Proc T_in T_out'
       Normal interrupt handling: interrupts an attacker should not
       know about leak through scheduling.

     model_good         : Proc T_in T_out'
       Interrupt masking is controlled so that secret interrupts can
       be received without leaking.  Shows every process-pool output
       (user space, scheduler and all handlers).

     wrapped_model_good : Proc T_in T_out
       The final model: a wrapper around model_good exposing only the
       user-space outputs.

   Contents:
     1. Userspace processes, scheduler and interrupt handler
     2. Process pool
     3. Stateful wrapper
     4. Model state
     5. State transitions
     6. Trace vocabulary
     7. model_bad
     8. model_good
     9. wrapped_model_good
   ================================================================= *)

(* A note on notation.  Processes have type [Proc I O] where I and O range over
   the inductive [Ty] of interface types, and [ [t] ] denotes the Coq type that
   [t : Ty] encodes.  Indexing by [Ty] rather than by Coq's [Set] is what makes
   reductions invertible in the proofs, but it also forces the explicit [@] and
   [Ty] annotations below.  To keep the constructions readable, each process
   definition is preceded by a comment giving the same term with those
   annotations erased. *)


(* === 1. Userspace processes, scheduler and interrupt handler === *)

(* low_p = out GetRequest *)

Definition low_p := @out Unit TPublicOutput GetRequest.


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
(* high_p = alternate Syscall NOP tt (fun i => i == Notify) *)
Definition high_p := @alternate THandlerOutput TTypeSyscall Unit Syscall NOP tt (fun i => i == Notify).

(* scheduler =
     map id (fun o => o.1 + 2)
       (sta (fun _ v => v) (fun _ v => v.+1 %% 2) 1 (out tt)) *)
Definition scheduler : Proc Empty Nat :=
  map (O := Times Nat Unit) (O' := Nat) id
    (fun o => o.1 + 2)                        (*skip the interrupt handlers to reach high_p and low_p*)
    (sta (V := Nat) (O := Unit)
       (fun _ v => v) (fun _ v => v.+1 %% 2)
       1                                      (*will start scheduling the high process*)
       (out (O := Unit) tt)).

Definition handler_type := Proc Unit THandlerOutput.

(* I_handler =
     map id (fun o => if o.1 == 0 then Notify else Nothing)
       (sta (fun _ v => v) (fun _ v => v.+1 %% 2) 0 (out tt)) *)
Definition I_handler : handler_type :=
  map (O := Times Nat Unit) (O' := THandlerOutput) id
    (fun o => if o.1 == 0 then Notify else Nothing)
    (sta (V := Nat) (O := Unit)
       (fun _ v => v) (fun _ v => v.+1 %% 2)
       0
       (out (O := Unit) tt)).

Definition my_f_I (n : nat) :=
  match n with
  | 0 => Unit (*tI*)
  | 1 => Unit (*dI*)
  | 2 => Unit (*defaultI*)
  | 3 => Empty (*scheduler*)         
  | 4 => THandlerOutput (*high*)
  | 5 => Unit (*low*)
  | _ => Unit (*padding*)           
  end.

Definition my_f_O (n : nat) :=
  match n with
  | 0 => THandlerOutput (*tI*)
  | 1 => THandlerOutput (*dI*)
  | 2 => THandlerOutput (*defaultI*)
  | 3 => Nat (*scheduler*)         
  | 4 => TTypeSyscall (*high*)
  | 5 => TPublicOutput (*low*)
  | _ => Unit (*padding*)           
  end.

(* unit_proc = out tt *)
Definition unit_proc : Proc Unit Unit := out (O := Unit) tt.

(* -- Indexed family of processes -- *)
Definition my_procs : forall n, Proc (my_f_I n) (my_f_O n) :=
  fun n => match n with
           | 0        (*timer interrupt handler*)
           | 1        (*disk interrupt handler*)
           | 2        (*default handler*)
             => I_handler
           | 3 => scheduler
           | 4 => high_p
           | 5 => low_p
           | _ => unit_proc (*padding*)
           end.


(* === 2. Process pool === *)

(* process_pool n f_coopt f_initial f_I f_O f_proj f_pid f_proc =
     match n with
     | 0 =>
         map (fun i => (f_pid i.1 == 0, f_proj i.2 0)) id
           (swi (f_initial 0) (maybe (map id (fun o => (f_coopt 0, o)) (f_proc 0))))
     | n0.+1 =>
         par (map (fun i => (f_pid i.1 == n0.+1, f_proj i.2 n0.+1)) id
                (swi (f_initial n0.+1) (maybe (map id (fun o => (f_coopt n0.+1, o)) (f_proc n0.+1)))))
             (process_pool n0 f_coopt f_initial f_I f_O f_proj f_pid f_proc)
     end *)
Fixpoint process_pool
  (cur_pid : Ty)
  (n : nat)
  (f_coopt : nat -> bool)
  (f_initial : nat -> bool)
  (f_I f_O : nat -> Ty)
  (T' : Ty)
  (f_proj : [T'] -> forall n, [(Option (f_I n))])
  (f_pid : [cur_pid] -> [Nat])
  (f_proc : forall n, Proc (f_I n) (f_O n)) {struct n}
  : Proc (Times cur_pid T') (times_on n f_O) :=
  (* process n: gate the input by [f_pid = n], run [f_proc n] behind a switch, and
     par it with the pool for the remaining processes. *)
  match n as n1 return Proc (Times cur_pid T') (times_on n1 f_O) with
  | 0 =>
      map ((fun i => (f_pid i.1 == 0, f_proj i.2 0))
             : [Times cur_pid T'] -> [Times Bool (Option (f_I 0))]) id
          (swi (f_initial 0)
             (maybe (map id ((fun o => (f_coopt 0, o)) : [f_O 0] -> [Times Bool (f_O 0)]) (f_proc 0))))
  | n0.+1 =>
      par (map ((fun i => (f_pid i.1 == n0.+1, f_proj i.2 n0.+1))
                  : [Times cur_pid T'] -> [Times Bool (Option (f_I n0.+1))]) id
               (swi (f_initial n0.+1)
                  (maybe (map id ((fun o => (f_coopt n0.+1, o)) : [f_O n0.+1] -> [Times Bool (f_O n0.+1)]) (f_proc n0.+1)))))
          (@process_pool cur_pid n0 f_coopt f_initial f_I f_O T' f_proj f_pid f_proc)
  end.

Definition cur_pid := Sum Bool Nat.
Definition initial_pid : [cur_pid] := inr 3. (*starting with low process*)

Definition my_f_coopt (n : nat) : bool := true.

Definition my_f_pid (pid : [cur_pid]) : [Nat] :=
  match pid with
  | inl true => 1 (*disk interrupt*)
  | inl false => 2 (*default interrupt*)
  | inr 0 => 0
  | inr 1 => 3
  | inr 2 => 4
  | inr 3 => 5
  | inr n => n             
  end.

Definition my_f_initial (n : nat) := n == (my_f_pid initial_pid).

Definition T_intermediate := Option THandlerOutput.
Definition f_proj (i : [T_intermediate]) : forall n, [Option (my_f_I n)] :=
  fun n => match n with
           | 4 => i     (*the high process receives the disk-interrupt handler's output*)
           | _ => None  (*every other process receives nothing*)
           end.

(* my_process_pool =
     process_pool 5 my_f_coopt my_f_initial my_f_I my_f_O T_intermediate f_proj my_f_pid my_procs *)
Definition my_process_pool := @process_pool cur_pid 5 my_f_coopt my_f_initial my_f_I my_f_O T_intermediate f_proj my_f_pid my_procs.


(* === 3. Stateful wrapper === *)

Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.
(*We define a stateful wrapper that will be wrapped around the process pool*)
(* loop_sta state f_I def p f_si =
     map inl (inr_or_def def)
       (loop (map id snd
         (sta f_I (fun _ v => v) state
           (map f_si inr (maybe p))))) *)
Definition loop_sta
  (cur_pid stateType : Ty)           
  (state : [stateType])
  (T_in T_out T' : Ty)                
  (f_I : [Sum T_in T_out] -> [stateType] -> [stateType])
  (def : [T_out])
  (p : Proc (Times cur_pid T') T_out)
  (f_si : [Times stateType (Sum T_in T_out)] -> [Option (Times cur_pid T')])
  : Proc T_in T_out :=
  (@map T_in (Sum T_in T_out) (Sum T_in T_out) T_out inl (inr_or_def def)
                          (@loop (Sum T_in T_out)
                             (@map _ _ (Times _ _) _
                                id snd
                                (@sta _ _ stateType f_I (fun _ v => v) state
                                   (@map (Times stateType (Sum _ _ ))
                                      (Option (Times cur_pid T')) _ (Sum T_in T_out) f_si inr (maybe p)))))).


(* === 4. Model state === *)
Definition mask := Bool.
Definition pending := Bool.
Definition I_bits := Times pending mask.
Definition ir_count := Option Nat.
Definition ic := Times I_bits (Times I_bits I_bits).
Definition count := Nat.
Definition re_sch := Bool.
Definition prev_pid := Option Nat.
Definition pids := Times cur_pid prev_pid.
(* ic_count bundles the interrupt-handler time slice with the interrupt controller.
   ir_count = None  -> feature disabled
   ir_count = Some n -> n steps of handler execution left; Some 0 -> return to user space *)
Definition ic_count := Times ir_count ic.
Definition bool_state := Times re_sch ic_count.
Definition all_interrupts : seq [TInterrupt] :=
  [:: TimerInterrupt; DiskInterrupt; DefaultInterrupt].
Definition sans_timer : seq [TInterrupt] :=
  [:: DiskInterrupt; DefaultInterrupt].
Definition stateType := Times pids bool_state.

Definition get_pids (v : [stateType]) := v.1.
Definition get_bool_state (v : [stateType]) := v.2.
Definition get_cur_pid (v : [stateType]) := (get_pids v).1.
Definition get_prev_pid (v : [stateType]) := (get_pids v).2.
Definition get_re_sch (v : [stateType]) := (get_bool_state v).1.
Definition get_ic_count (v : [stateType]) := (get_bool_state v).2.
Definition get_ir_count (v : [stateType]) := (get_ic_count v).1.
Definition get_ic (v : [stateType]) := (get_ic_count v).2.

Definition get_I_bits' (ic : [ic]) (ir : [TInterrupt]) : [I_bits] :=
  match ir with
  | DefaultInterrupt => ic.1 
  | DiskInterrupt    => ic.2.1
  | TimerInterrupt => ic.2.2
  end.
Definition get_I_bits (v : [stateType]) (ir : [TInterrupt]) := get_I_bits' (get_ic v) ir.

Definition get_pending' (bits : [I_bits]) := bits.1.
Definition get_mask' (bits : [I_bits]) := bits.2.

Definition get_I_pending (v : [stateType]) (ir : [TInterrupt]) := get_pending' (get_I_bits v ir).
Definition get_I_mask (v : [stateType]) (ir : [TInterrupt]) := get_mask' (get_I_bits v ir).

Definition update_pids (v : [stateType]) pids : [stateType] := (pids,v.2).
Definition update_bool_state (v : [stateType]) bs : [stateType] := (v.1,bs).
Definition update_cur_pid (v : [stateType]) cur_pid : [stateType] := update_pids v (cur_pid,(get_pids v).2).
Definition update_prev_pid (v : [stateType]) prev_pid : [stateType] := update_pids v ((get_pids v).1,prev_pid).
Definition update_re_sch (v : [stateType]) re_sch : [stateType] := update_bool_state v (re_sch,(get_bool_state v).2).

Definition update_I_bits' (myic : [ic]) (ir : [TInterrupt]) (bits : [I_bits]) : [ic] :=
  match ir with
  | DefaultInterrupt => (bits, myic.2)
  | DiskInterrupt    => (myic.1, (bits, myic.2.2))
  | TimerInterrupt => (myic.1, (myic.2.1, bits))
  end.

Definition update_ic_count (v : [stateType]) icc : [stateType] := update_bool_state v ((get_bool_state v).1,icc).
Definition update_ir_count (v : [stateType]) c : [stateType] := update_ic_count v (c,(get_ic_count v).2).
Definition update_ic (v : [stateType]) ic : [stateType] := update_ic_count v ((get_ic_count v).1,ic).
Definition update_I_bits (v : [stateType]) (ir : [TInterrupt]) (bits : [I_bits]) := update_ic v (update_I_bits' (get_ic v) ir bits).

Definition update_I_pending (v : [stateType]) (ir : [TInterrupt]) pending : [stateType] :=
  update_I_bits v ir (pending,get_I_mask v ir).
Definition update_I_mask (v : [stateType]) (ir : [TInterrupt ]) mask : [stateType] :=
  update_I_bits v ir (get_I_pending v ir,mask).

Definition or_I_bits (b1 b2 : [I_bits]) : [I_bits] := (b1.1 || b2.1, b1.2 || b2.2).
Definition or_ic (c1 c2 : [ic]) : [ic] :=
  (or_I_bits c1.1  c2.1,
   (or_I_bits c1.2.1 c2.2.1,
    or_I_bits c1.2.2 c2.2.2)).
(* keep the base state's time slice (s1.2.1); only the interrupt controller is merged *)
Definition or_bool_state (s1 s2 : [bool_state]) : [bool_state] := (s1.1 || s2.1, (s1.2.1, or_ic s1.2.2 s2.2.2)).

Definition set_masks (v : [stateType]) : [stateType] :=
  foldr (fun I v' => update_I_mask v' I true) v all_interrupts.
Definition unset_masks (v : [stateType]) : [stateType] :=
  foldr (fun I v' => update_I_mask v' I false) v all_interrupts.
Definition unset_masks_sans (v : [stateType]) : [stateType] :=
  foldr (fun I v' => update_I_mask v' I false) v sans_timer.
Definition unset_tI (v : [stateType]) : [stateType] := update_I_mask v TimerInterrupt false.
Definition set_tI (v : [stateType]) : [stateType] := update_I_mask v TimerInterrupt true.
Definition set_otherIs (v : [stateType]) : [stateType] := foldr (fun I v' => update_I_mask v' I true) v sans_timer.
Definition masks_set (v : [stateType]) :=
  foldr (fun I b => (get_I_mask v I) && b) true all_interrupts.


(* === 5. State transitions === *)
Definition step_left (f : [T_in] -> [stateType] -> [stateType]) : [Sum T_in T_out'] -> [stateType] -> [stateType] :=
  fun i v => 
  match i with
  | inl i => f i v
  | inr _ => v
  end.

Definition step_right (f : [T_out'] -> [stateType] -> [stateType]) : [Sum T_in T_out'] -> [stateType] -> [stateType] :=
  fun i v => 
  match i with
  | inl _ => v
  | inr o => f o v
  end.

Definition step0 := step_left (fun i v => update_I_pending v i true).

Definition is_sch_out (o : [T_out']) :=
  match o with
  | (None,(None,(Some n,_))) => Some n
  | _ => None                                   
  end.
Definition check_scheduler (o : [T_out']) (v : [stateType])  :=
  if @is_sch_out o is Some n then update_cur_pid v (inr n) else v.

Definition step1 := step_right check_scheduler.

Definition nat_to_cur_pid (n : nat) : [cur_pid ] :=
  match n with
  | 0 => inr 0 (*timer interrupt*)
  | 1 => inl true (*disk interrupt*)
  | 2 => inl false (*default interrupt*)
  | 3 => inr 1 (*scheduler*)
  | 4 => inr 2 (*high p*)
  | 5 => inr 3 (*low p*)
  | n => inr n             
  end.
Definition I_handler_pid (ir : [TInterrupt]) : [cur_pid] :=
  nat_to_cur_pid (index ir all_interrupts).

(* before overriding cur_pid, save it to prev_pid if it is a user process *)
Definition save_cur_to_prev (v : [stateType]) : [stateType] :=
  if get_cur_pid v is inr n
  then update_prev_pid v (Some n)
  else v.

Definition initiate_handler (ir : [TInterrupt]) (v : [stateType]) :=
  update_I_pending (set_masks (update_cur_pid (save_cur_to_prev v) (I_handler_pid ir))) ir false.

(* a handler is selectable iff pending and not masked *)
Definition I_ready (v : [stateType]) (ir : [TInterrupt]) : bool :=
  get_I_pending v ir && ~~ get_I_mask v ir.

Definition first_ready (v : [stateType]) : option [TInterrupt] :=
  ohead [seq ir <-  all_interrupts | (I_ready v ir) ].

Definition is_handler_pid (v : [stateType]) :=
    match get_cur_pid v with
    | inr 0 => true
    | inr _ => false
    | _ => true             
    end.

Definition scheduler_pid : [cur_pid] := inr 1.

Definition initiate_scheduler  (v : [stateType]) := update_re_sch (update_prev_pid (update_cur_pid v scheduler_pid) None) false.

Definition get_prev_pid_wrap (v : [stateType]) : [Option cur_pid] := if get_prev_pid v is Some n then Some (inr n) else None.
Definition initiate_prev_pid  (v : [stateType]) := update_prev_pid (update_cur_pid v (odflt scheduler_pid (get_prev_pid_wrap v))) None.

Definition initiate_next (bool_coding :  [stateType] -> [stateType]) :  [stateType] -> [stateType] :=
  fun v => if (masks_set v) then v (*handler running*) else
             let v := bool_coding v (*apply time slice logic to bools*) in
             if first_ready v is Some ir then initiate_handler ir v (*first or later handler in the time slice is initiated here, enforced that at least one will run due to bool_coding*) else
               if is_handler_pid v then if get_re_sch v then initiate_scheduler v else initiate_prev_pid v  (*mask not set but we are in handler pid, we have just finished the time slice*) else
                 v (*we are running in user space*).
                          


Definition state_step (handler_preroutine : [T_out'] -> [stateType] -> [stateType]) (bool_coding : [stateType] -> [stateType]) (i : [Sum T_in T_out']) : [stateType] -> [stateType] :=
  (step_right (fun i => initiate_next bool_coding) i) \o (step_right handler_preroutine i) \o (step1 i) \o (step0 i).
(*we wrap initiate_next in step_right even though it does not use the input to ensure we only apply this step on output updates, this is important for the last case of f_EP for initiate_next*)


(* === 6. Trace vocabulary === *)
(* Named inputs and outputs used to write the example traces for each model. *)
Definition Tsum' := ([T_in] + [T_out'])%type.
Definition Tsum := Sum T_in T_out. 

Definition dI' : Tsum' := inl DiskInterrupt.
Definition tI' : Tsum' := inl TimerInterrupt. 
Definition low_out x : [T_out'] := (Some x,(None,(None,(None,(None,None))))).
Definition high_out x : [T_out'] := (None,(Some x,(None,(None,(None,None))))).
Definition sch_o x : [T_out'] := (None,(None,(Some x,(None,(None,None))))).
Definition defaultI_o x : [T_out'] := (None,(None,(None,(Some x,(None,None))))).
Definition dI_o x : [T_out'] := (None,(None,(None,(None,(Some x,None))))).
Definition tI_o x : [T_out'] := (None,(None,(None,(None,(None,Some x))))).

Definition tI_yes' : Tsum' :=  inr (tI_o (Notify)).
Definition tI_no' : Tsum' :=  inr (tI_o (Nothing)).

Definition dI_yes' : Tsum' :=  inr (dI_o (Notify)).
Definition dI_no' : Tsum' :=  inr (dI_o (Nothing)).

Definition pub_get' : Tsum' := inr (low_out GetRequest).
Definition pr_nop' : Tsum' := inr (high_out NOP).
Definition pr_sys' : Tsum' := inr (high_out Syscall).

Definition sch_low : Tsum' := inr (sch_o 3).
Definition sch_high : Tsum' := inr (sch_o 2).

Definition defaultI_no' : Tsum' :=  inr (defaultI_o (Nothing)).
Definition defaultI_yes' : Tsum' :=  inr (defaultI_o (Notify)).

Definition pub_get : [Tsum] := inr (Some (inl (GetRequest))).
Definition pr_nop : [Tsum] := inr (Some (inr NOP)).
Definition pr_sys : [Tsum] := inr (Some (inr Syscall)).
Definition w_None : [Tsum] := inr None.
Definition tI : [Tsum] := inl TimerInterrupt.
Definition dI : [Tsum] := inl DiskInterrupt.

Definition seqtype' := seq Tsum'.
Definition seqtype := seq ([T_in] + [T_out]).




(* === 7. model_bad === *)

Definition false_I_bits : [I_bits] := (false,false).
Definition false_ic : [ic] := ((false,false),(false_I_bits,false_I_bits)).
Definition initial_state : [stateType] := ((initial_pid,None),(false,(None,false_ic))).

Definition tI_out (o : [T_out']) :=
  match o with
  | (_,(_,(_,(_,(_,x))))) => x
  end.


Definition dI_out (o : [T_out']) :=
  match o with
  | (_,(_,(_,(_,(x,_))))) => x
  end.

Definition default_I_out (o : [T_out']) :=
  match o with
  | (_,(_,(_,(x,(_,_))))) => x
  end.  

Definition is_I_out_done (o : [T_out']) : [Option TInterrupt] :=
  if tI_out o is Some Notify then Some TimerInterrupt
  else if dI_out o is Some Notify then Some DiskInterrupt
  else if default_I_out o is Some Notify then Some DefaultInterrupt
  else None.  

Definition bad_preroutine (o : [T_out']) (v : [stateType])  :=
  if is_I_out_done o is Some ir then let v := unset_masks v in if ir is TimerInterrupt then update_re_sch v true else v else v.

Definition def : [ T_out' ]  := (None,(None,(None,(None,(None,None))))).

(*discards input from the inner process, only allowed to affect bit in ic, not pid*)
Definition f_si (si : [Times stateType (Sum T_in T_out')]) : [Option (Times cur_pid T_intermediate)] :=
  if si.2 is inr o then Some (get_cur_pid si.1, dI_out o) else None.

(* model_bad = loop_sta initial_state (state_step bad_preroutine id) def my_process_pool f_si *)
Definition model_bad : Proc T_in T_out' := @loop_sta cur_pid stateType initial_state T_in T_out' T_intermediate (state_step bad_preroutine id) def my_process_pool f_si.



(* model_bad traces *)
Definition no_dI' : seqtype' :=   [::pub_get';                                     tI';pub_get';tI_no';tI_yes';sch_high;pr_nop'(*nop*);tI';pr_nop';tI_no';tI_yes';sch_low;pub_get'].
Definition with_dI' : seqtype' := [::pub_get';dI';pub_get';dI_no';dI_yes';pub_get';tI';pub_get';tI_no';tI_yes';sch_high;pr_sys'(*sys*);tI';pr_nop';tI_no';tI_yes';sch_low;pub_get'].

Ltac rewr := rewrite /model_bad /loop_sta /my_process_pool /process_pool /my_f_initial /low_p /my_f_coopt /alternate /high_p /f_si /tI_o /I_handler /f_proj /scheduler /low_out.

Ltac lsolv := try solve [ reduce_tac;reduce_tac | reduce_tac;try solve [reduce_once | econ];simpl;first (reduce_tac;reduce_tac)];simpl.
Ltac reduce_tac2 :=
  (try rewr);
   (repeat
      reduce_once);(try swi_instans); rewrite ?eqxx /= /xor /=.

Ltac sta_state_reduce :=
  match goal with
  | |- context [(@sta (Sum T_in T_out') (Sum T_in T_out') stateType (state_step _ _) _ ?state _)] =>let reduced := eval cbv in state in
                                                                                                          pattern state; match goal with |- ?F state => change (F reduced) end; cbv beta
  end.                                                                                                             

Lemma trace_no_dI' : forall l, Trace (publicRel _) l no_dI' model_bad.
Proof.  
  intros.
  rewr;simpl;rewr;simpl;rewr;simpl;rewr.

  sta_state_reduce.

   do 12 (first [econ;[idtac | econ | idtac] | econ];
         reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).

  (*proved the last element of the trace manually to avoid evar holes in proof*)
   (first [econ;[idtac | econ | idtac] | econ];
    reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans).
   econ. reduce_tac2;reduce_tac2. econ. econ. reduce_tac. econ. econ.
   reduce_tac. econ. econ. reduce_tac. econ. econ. reduce_tac. econ.
   econ. reduce_tac. econ. econ. reduce_tac. econ.
Qed.

Lemma trace_with_dI' : forall l, Trace (publicRel _) l with_dI' model_bad.
Proof.
  intros.
  rewr;simpl;rewr;simpl;rewr;simpl;rewr.

  do 17(first [econ;[idtac | econ | idtac] | econ];
        reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).

  (*proved the last element of the trace manually to avoid evar holes in proof*)  
   (first [econ;[idtac | econ | idtac] | econ];
    reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans).
   econ. reduce_tac2;reduce_tac2. econ. econ. reduce_tac. econ. econ.
   reduce_tac. econ. econ. reduce_tac. econ. econ. reduce_tac. econ.
   econ. reduce_tac. econ. econ. reduce_tac. econ.
Qed.




(* === 8. model_good === *)
Definition mask_most : [ic] := ((false,true),((false,true),(false,false))). (*mask set for everything but timer interrupt*)

Definition init_ir_count : [ir_count] := Some 4.

Definition good_to_bs (ir : [TInterrupt]) (b : [Bool]) : [bool_state] :=
  let ic := ((~~b,b),((false,b),(false,~~b))) in
  let ic' := ((~~b,b),((false,b),(false,false))) in (*this one may not touch the timer interrupt mask because it depends on scheduling the private handlers*)
  
  (*~~b ensures tI is masked during the time slice, this prevents infering from toggling tI mask that defaultI/diskI handler has run (which toggles all masks. So in essence, the secret handlers may run, this sets the mask of tI, if we are not finished, e.g. b = false, then we mask again. If we are done, b = true, we don't mess with the unset tI mask*)
  (*We need ir = dI to ensure that it only runs once, which ensures that defaultI runs as the last one, this allows the termination signal to be public because the defaultI may output it*)
  match ir with
    | TimerInterrupt => (true,(None,ic))
    | DiskInterrupt => (false,(None,ic'))
  | DefaultInterrupt => (false,(None,ic'))
  end.

Definition initial_state_good : [stateType] := ((initial_pid,None),(false,(Some 0,mask_most))).

Definition handler_completed (c : [ir_count]) := match c with | Some 2 | Some 4 => true | _ => false end.

Definition initiate_ir (o : [T_out']) (v : [stateType]) : [stateType] :=
  if tI_out o is Some Notify then update_ir_count v (Some 4) else v.

Definition check_handler_completed (v : [stateType]) : [stateType] :=
  if handler_completed (get_ir_count v) then set_tI (unset_masks v) else v.

Definition check_ir_count (v : [stateType]) : [stateType] :=
    match (get_ir_count v) with
    | Some n.+1 => update_ir_count v (Some n)
    | Some 0 => update_ir_count (set_otherIs (unset_tI v)) None
    | None => v
    end.

(*this is composed with the finial step3 function, ensuring that the state space we need to reason about has the bool_coding constraints, i.e. defaultInterrupt pending will be true*)
Definition timeslice_live (c : [ir_count]) := match c with | Some n => 0 < n | _ => false end.

(*If timeslice is not live, we enforce that disk and default handlers are masked, and pending default is false.
 This allows us to infer that for v and v' that are related, that if v is ready as disk handler or default, then v' will also be ready.
 The reasoning chain is:
v is ready -> time slice is live for v -> time slice is live for v' -> pending for default is true (which combined with unset_handler_masks invariant that it always turns off masks when a handler is done, ensures that default handler always can fire if v can fire disk or default handler
 *)

Definition bool_coding v := let b := timeslice_live (get_ir_count v) in
                            let ic := (true,(None,((b,~~b),((false,~~b),(false,b))))) in
                            let v := update_bool_state v (or_bool_state (get_bool_state v) ic) in
                            let m := get_I_mask v DiskInterrupt in
                            update_I_mask v DefaultInterrupt m.

Definition good_preroutine (o : [T_out']) : [stateType] -> [stateType] := check_ir_count \o check_handler_completed \o (initiate_ir o). (*\o (unset_handler_masks o)*) 

(* model_good = loop_sta initial_state_good (state_step good_preroutine bool_coding) def my_process_pool f_si *)
Definition model_good := @loop_sta cur_pid stateType initial_state_good T_in T_out' T_intermediate (state_step good_preroutine bool_coding) def my_process_pool f_si.

(* model_good traces *)
Definition good_no_dI' : seqtype' :=   [::pub_get';                      tI';pub_get';tI_no';tI_yes';defaultI_no';defaultI_yes';defaultI_no';defaultI_yes';sch_high;pr_nop'(*nop*);tI';pr_nop';tI_no';tI_yes';defaultI_no';defaultI_yes';defaultI_no';defaultI_yes';sch_low;pub_get'].
Definition good_with_dI' : seqtype' := [::pub_get';dI';pub_get';pub_get';tI';pub_get';tI_no';tI_yes';dI_no'      ;dI_yes'      ;defaultI_no';defaultI_yes';sch_high;pr_sys'(*sys*);tI';pr_nop';tI_no';tI_yes';defaultI_no';defaultI_yes';defaultI_no';defaultI_yes';sch_low;pub_get'].


Ltac rewr ::= rewrite /model_bad /loop_sta /my_process_pool /process_pool /my_f_initial /low_p /my_f_coopt /alternate /high_p /f_si /tI_o /I_handler /f_proj /scheduler /low_out /model_good /my_process_pool /f_si /f_proj.

Lemma trace_good_no_dI' : forall l, Trace (publicRel _) l good_no_dI' model_good.
Proof.  
  intros.
  rewr;simpl;rewr;simpl;rewr;simpl;rewr.

  do 20(first [econ;[idtac | econ | idtac] | econ];
        reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).

   (first [econ;[idtac | econ | idtac] | econ];
    reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans).
   econ. reduce_tac2;reduce_tac2. econ. econ. reduce_tac. econ. econ.
   reduce_tac. econ. econ. reduce_tac. econ. econ. reduce_tac. econ.
   econ. reduce_tac. econ. econ. reduce_tac. econ.
Qed.

Lemma trace_good_with_dI' : forall l, Trace (publicRel _) l good_with_dI' model_good.
Proof.  
  intros.
  rewr;simpl;rewr;simpl;rewr;simpl;rewr.

  do 23(first [econ;[idtac | econ | idtac] | econ];
        reduce_tac;try solve [reflexivity| reduce_tac;reduce_tac];simpl;try swi_instans;sta_state_reduce).

   (first [econ;[idtac | econ | idtac] | econ];
    reduce_tac2;try solve [reflexivity| reduce_tac2;reduce_tac2];simpl;try swi_instans).
   econ. reduce_tac2;reduce_tac2. econ. econ. reduce_tac. econ. econ.
   reduce_tac. econ. econ. reduce_tac. econ. econ. reduce_tac. econ.
   econ. reduce_tac. econ. econ. reduce_tac. econ.
Qed.




(* === 9. wrapped_model_good === *)
Definition parse_output (o : [T_out']) : [T_out] :=
  match o with
  | (Some public,_) => Some (inl public)
  | (None,(Some prv,_)) => Some (inr prv)
  | _ => None
  end.


Definition wrapped_model_good : Proc T_in T_out := map id parse_output model_good.

(* wrapped_model_good traces *)
Definition final_out_rel : myrel [T_out] := eqmaybe_false (eqsum (publicRel _) (semiprivateRel _)).



Definition map_tr (I O O' : Ty) (f : [O] -> [O']) (s : seq ([I] + [O])) := seq.map (fun x => match x with | inl x' => inl x' | inr y => inr (f y) end) s.
Lemma Trace_map : forall (A B B' : Ty) (p : Proc A B) (f : [B] -> [B']) (s : seq ([A] + [B])) (BRel : myrel [B]) (BRel' : myrel [B']) l,
    f_NI BRel BRel' f ->
    Trace BRel l s p -> Trace BRel' l (map_tr f s) (map id f p).
Proof.  
  intros.
  elim : H0;ssa.
  econ. econ. econ. eauto. done.
  econ. econ. econ. eauto. apply H. done. done.
Qed.


Definition good_no_dI : seqtype :=   [::pub_get;                      tI;pub_get;w_None;w_None;w_None;w_None;w_None;w_None;w_None;pr_nop(*nop*);tI;pr_nop;w_None;w_None;w_None;w_None;w_None;w_None;w_None;pub_get].
Definition good_with_dI : seqtype := [::pub_get;dI;pub_get;pub_get;tI;pub_get;w_None;w_None;w_None      ;w_None      ;w_None;w_None;w_None;pr_sys(*sys*);tI;pr_nop;w_None;w_None;w_None;w_None;w_None;w_None;w_None;pub_get].

Lemma good_no_dI_eq : map_tr parse_output good_no_dI' = good_no_dI.
Proof. ssa. Qed.

Lemma good_with_dI_eq : map_tr parse_output good_with_dI' = good_with_dI.
Proof. ssa. Qed.

Lemma trace_no_dI : forall l, Trace (publicRel _) l good_no_dI wrapped_model_good.
Proof.
  intros. rewrite -good_no_dI_eq. eapply Trace_map.
  2:eapply trace_good_no_dI'.
  mrw. ssa. subst. done.
Qed.

Lemma trace_with_dI : forall l, Trace (publicRel _) l good_with_dI wrapped_model_good.
Proof.
  intros. rewrite -good_with_dI_eq. eapply Trace_map.
  2:eapply trace_good_with_dI'.
  mrw. ssa. subst. done.
Qed.  

