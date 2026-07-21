
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

Require Export NonInterference.theorems.

Fixpoint times_n n (f : nat -> Ty) : Ty :=
  let t := f n in
  match n with
  | 0 => t
  | S n' => Times t (times_n n' f)
  end.

Definition map_pair {A B C D :Set} (f : A -> C) (g : B -> D) := fun (x: A * B) => match x with
                                                                                | (x0,x1) => (f x0, g x1)
                                                                                  end.
Definition times_on (n : nat) (f : nat -> Ty) := times_n n (Option \o f).



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

(*sta_swi b n f p:
 (i == n,I') -> enables p
 (i <> n,I') -> disables p
 f projects input from pair e.g. f (I1,I2) = I1*)
Definition sta_swi (I O : Ty) (b : bool) (p : Proc I O) :=
@map _ _ (Times _ _) _ id snd
  (@sta (Times Bool _) _ Bool
       (fun i v => xor (fst i) v)
       (fun o v => false)
       b
       ( @map (Times Bool (Times Bool _)) (Times Bool _) _ _
          (fun i => (fst i,snd (snd i)))
          id
          (swi b (@map _ _ _ (Times Bool _)
                    id
                    (fun o => (false,o))
                    (p)
  )))).



Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.


Definition mask := Bool.
Definition pending := Bool.
Definition I_bits := Times pending mask.
Definition ir_count := Option Nat.
Definition ic := Times I_bits (Times I_bits I_bits).
Definition count := Nat.
Definition re_sch := Bool.
Definition prev_pid := Option Nat.
Definition cur_pid := Sum Bool Nat. (*false = defaultInterrupt, true=diskInterrupt*)
(*Definition pids := Times cur_pid prev_pid.*)
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
  | DefaultInterrupt => ic.1  (*default pending is always true*)
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
  | DefaultInterrupt => (bits, myic.2)         (* keep only the mask; discard pending *)
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

Definition my_f_I := fun (n : nat) => if n == 4 then THandlerOutput else if n == 3 then Empty else  Unit.

(*Definition I_output_type := Times THandlerOutput bool_state.*)

Definition my_f_O := fun (n : nat) => if n == 3 then Nat else if n == 4 then TTypeSyscall else if n == 5 then TPublicOutput else THandlerOutput.


Definition T_in := TInterrupt.
Definition T_out' := Times (Option TPublicOutput) (Times (Option TTypeSyscall) (Times (Option Nat) (times_on 2 (fun _ => THandlerOutput)))).
Definition T' := Option THandlerOutput.
Definition is_sch_out (o : [T_out']) :=
  match o with
  | (None,(None,(Some n,_))) => Some n
  | _ => None                                   
  end.

(*Definition all_interrupts : seq [TInterrupt] := [::TimerInterrupt;DiskInterrupt].*)
Definition n_to_I (v : [stateType]) (n : nat) := nth TimerInterrupt all_interrupts n.

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


Definition is_user_pid (p : [cur_pid]) : bool := if p is inr _ then true else false.
Definition is_sch (p : [cur_pid]) : bool := p == inr 1.
Definition scheduler_pid : [cur_pid] := inr 1.

(*we distinguish disk and default interrupt handler because their output is secret*)
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

(* a handler is selectable iff pending and not masked *)
Definition I_ready (v : [stateType]) (ir : [TInterrupt]) : bool :=
  get_I_pending v ir && ~~ get_I_mask v ir.

Definition first_ready (v : [stateType]) : option [TInterrupt] :=
  ohead [seq ir <-  all_interrupts | (I_ready v ir) ].

(* before overriding cur_pid, save it to prev_pid if it is a user process *)

(*Definition update_prev_pid_wrap (v : [stateType]) (n : [cur_pid]) : [stateType] :=
  if n is inr n' then update_prev_pid v (Some n') else v.*)

Definition save_cur_to_prev (v : [stateType]) : [stateType] :=
  if get_cur_pid v is inr n
  then update_prev_pid v (Some n)
  else v.


Definition false_I_bits : [I_bits] := (false,false).
Definition false_ic : [ic] := ((false,false),(false_I_bits,false_I_bits)).


  


(*Definition step_on_input (i : [T_in]) (v : [stateType]) : [stateType] :=*)

(*Definition check_ir_count (o : [T_out']) (v : [stateType]) : [stateType] :=
  if get_ir_count v is None then v else
  if is_I_out_done o is Some TimerInterrupt then update_ir_count v (Some 4) else if get_ir_count v is Some n then update_ir_count v (Some n.-1) else v.*)

Definition check_scheduler (o : [T_out']) (v : [stateType])  :=
  if @is_sch_out o is Some n then update_cur_pid v (inr n) else v.

(*Definition check_tI (to_bs : [TInterrupt] -> [Bool] -> [bool_state]) (o : [T_out']) (v : [stateType])  :=
  if is_I_out_done o is Some  then
    update_bool_state v (or_bool_state (get_bool_state (unset_masks v)) (to_bs ir ((get_ir_count v) == (Some 0)))) else v.*)



Definition initiate_handler (ir : [TInterrupt]) (v : [stateType]) :=
  update_I_pending (set_masks (update_cur_pid (save_cur_to_prev v) (I_handler_pid ir))) ir false.

Definition initiate_scheduler  (v : [stateType]) := update_re_sch (update_prev_pid (update_cur_pid v scheduler_pid) None) false.

Definition get_prev_pid_wrap (v : [stateType]) : [Option cur_pid] := if get_prev_pid v is Some n then Some (inr n) else None.
Definition initiate_prev_pid  (v : [stateType]) := update_prev_pid (update_cur_pid v (odflt scheduler_pid (get_prev_pid_wrap v))) None.

(*Definition inspect_output (to_bs : [TInterrupt] -> [Bool] -> [bool_state]) (o : [T_out']) : [stateType] -> [stateType] :=
  (check_handlers to_bs o) \o check_scheduler o.*)

Definition compute_next_pid (o : [T_out']) (v : [stateType]) : [stateType] :=
  match first_ready v with
  | Some ir => initiate_handler ir v 
  | None => if is_I_out_done o is None then v
            else if (get_re_sch v)
                 then initiate_scheduler v
                 else initiate_prev_pid v
  end.

(*Definition step_on_output (to_bs : [TInterrupt] -> [Bool] -> [bool_state]) (o : [T_out']) : [stateType] -> [stateType]:=
  (compute_next_pid o) \o (inspect_output to_bs o).*)

Lemma sta_comp : forall (I V O : Ty) (IRel : myrel [I]) (VRel : myrel [V]) (ORel : myrel [O]) (f f' : [I] -> [V] -> [V]) (g : [O] -> [V] -> [V])
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

Definition is_handler_pid (v : [stateType]) :=
    match get_cur_pid v with
    | inr 0 => true
    | inr _ => false
    | _ => true             
    end.

Definition initiate_next :  [stateType] -> [stateType] := fun v =>  if first_ready v is Some ir then
                                                                                             initiate_handler ir v
                                                                                           else if (~~ masks_set v) && (is_handler_pid v) then  if get_re_sch v then initiate_scheduler v else initiate_prev_pid v
                                                                                                else v.
                                                                                                  
                                                                                                                 
(*Definition maybe_initiate_scheduler :  [T_out'] -> [stateType] -> [stateType] := fun o v => if first_ready v is Some _ then v else if is_I_out_done o is None then v else if get_re_sch v then initiate_scheduler v else v.
Definition maybe_initiate_prev_pid : [T_out'] -> [stateType] -> [stateType] := fun o v => if first_ready v is Some _ then v else if is_I_out_done o is None then v else if ~~ get_re_sch v then initiate_prev_pid v else v.*)
Definition step0 := step_left (fun i v => update_I_pending v i true).

Definition dec_ir_count (c : [ir_count]) : [ir_count] :=
  if c is Some n then Some n.-1 else None.


(*Definition step0' := step_right check_ir_count.*)
Definition step1 := step_right check_scheduler.
(*Definition step2  (to_bs : [TInterrupt] -> [Bool] -> [bool_state]) := step_right (check_handlers to_bs).*)
(*Definition step3 := step_right initiate_next.*)
(*Definition step4 := step_right maybe_initiate_scheduler.
Definition step5 := step_right maybe_initiate_prev_pid.*)


Definition state_step (handler_preroutine : [T_out'] -> [stateType] -> [stateType]) (bool_coding : [stateType] -> [stateType]) (i : [Sum T_in T_out']) : [stateType] -> [stateType] :=
  (initiate_next \o bool_coding) \o (step_right handler_preroutine i) \o (step1 i) \o (step0 i).


(*Definition f_I (to_bs : [TInterrupt] -> [Bool] -> [bool_state]) (i : [Sum T_in T_out']) (v : [stateType]) : [stateType] :=
  match i with
  | inl i => 
  | inr o => let v := if @is_sch_out o is Some n then update_cur_pid v n else v in (*apply scheduler choice, lowest priority*)
             let v:= if is_I_out_done o is Some (ir,b) then
                         update_bool_state v (or_bool_state (get_bool_state (unset_masks v)) (to_bs ir b)) else v in
             match first_ready v with
             | Some ir => (update_I_pending (set_masks (update_cur_pid (save_cur_to_prev v) (I_handler_pid ir))) ir false)
             | None => if is_I_out_done o is None then v
                       else if (get_re_sch v)
                            then update_re_sch (update_prev_pid (update_cur_pid v handler_pid) None) false
                            else update_prev_pid (update_cur_pid v (odflt handler_pid (get_prev_pid v))) None
             end
  end.*)

(*We only reroute disk interrupts*)
(*Definition is_I_out (o : [T_out']) : [Option THandlerOutput] :=
if dI_out o is Some (o',_) then Some o'
       else None.*)

(*discards input from the inner process, only allowed to affect bit in ic, not pid*)
Definition f_si (si : [Times stateType (Sum T_in T_out')]) : [Option (Times cur_pid T')] :=
  if si.2 is inr o then Some (get_cur_pid si.1, dI_out o) else None.

Definition low_p := @out Unit TPublicOutput GetRequest.
Definition high_p := @alternate_generic2 THandlerOutput TTypeSyscall Unit1 Syscall NOP tt (fun i => i == Notify).

Definition handler_type := Proc Unit THandlerOutput.

Definition I_handler : handler_type.
  rewrite /handler_type.
  eapply map. exact id.
  instantiate (1:= Times Nat Unit).
  exact (fun o => if o.1 == 0 then Notify else Nothing).
  eapply sta. exact (fun _ v => v). exact (fun _ v => v.+1%%2).
  exact 0.
  apply out. exact tt.
Defined.

(*Definition bad_tI_handler : handler_type := I_handler. (*false_ic all of them*) (*re_sch = true only for timer interrupt handler*)
Definition bad_dI_handler : handler_type := I_handler.
Definition bad_default_handler : handler_type := I_handler.*)

Definition scheduler : Proc Empty Nat.
  eapply map. exact id.
  instantiate (1:= Times Nat Unit). exact (fun o => fst o + 2). (*skip first three processes to reach high_p (0) and low_p (1) *)
  eapply sta. exact (fun _ v => v). exact (fun _ v => v.+1%%2).
  exact 1. (*Will start scheduling high process*)
  apply out. exact tt.
Defined.

(*the only way handlers differ in what flags they set. This has been moved out of the handler itself and is interpreted from the Notify output
   they give. For example Notify from timer interrupt implies re_sch should be set to true. *)
Definition my_procs_bad : forall n, Proc (my_f_I n) (my_f_O n).
  case. apply I_handler. (*timer interrupt handler*)
  case. apply I_handler. (*disk interrupt handler*)
  case. apply I_handler. (*default handler*)
  case. cbv. apply scheduler.
  case. apply high_p.  
  case. apply low_p.
  elim. apply I_handler.
  intros. apply I_handler.
Defined.

Definition f_proj (i : [T']) : forall n, [Option (my_f_I n)].
  simpl. rewrite /my_f_I. intros. case_if.
  apply i.
  exact None. 
Defined.


Definition process_pool
  (n : nat)
  (f_coopt : nat -> bool)
  (f_initial : nat -> bool)
  (f_I f_O : nat -> Ty)  
  (T' : Ty)
  (f_proj : [T'] -> forall n, [(Option (f_I n))])
  (f_pid : [cur_pid] -> [Nat])
  (f_proc : forall n, Proc (f_I n) (f_O n)) : Proc (Times cur_pid T') (times_on n f_O).
  elim: n.
  - simpl.
    eapply map. simpl.
    instantiate (1:= Times Bool (Option (f_I 0))). exact (fun i => (f_pid i.1 == 0, f_proj i.2 0)). 
    exact id.  
    apply swi. exact (f_initial 0). 
    apply maybe. 
    eapply map.
      eapply id. 
      exact (fun o => (f_coopt 0,o)).
    exact (f_proc 0).

  - intros. rewrite /times_on. simpl.
    apply par.
    * eapply map.
      instantiate (1:= Times Bool (Option (f_I n.+1))). simpl.
      exact (fun i => (f_pid i.1 == n.+1,f_proj i.2 n.+1)).
        exact id. 
      eapply swi.
        exact (f_initial n.+1). 
      eapply maybe.
      eapply map.
        exact id.     
        exact (fun o => (f_coopt n.+1,o)).
      (*eapply maybe.*) (*not necessary anymore*)
        exact (f_proc n.+1).
        apply H.
Defined.

Definition my_f_coopt (n : nat) : bool := true.
Definition initial_pid : [cur_pid] := inr 3. (*starting with low process*)

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


Definition my_process_pool_bad := @process_pool 5 my_f_coopt my_f_initial my_f_I my_f_O T' f_proj my_f_pid my_procs_bad.
Definition initial_state : [stateType] := ((initial_pid,None),(false,(None,false_ic))).
Definition def : [ T_out' ]  := (None,(None,(None,(None,(None,None))))).


Definition loop_sta
  (stateType : Ty)           
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


(*Definition bad_to_bs (ir : [TInterrupt]) : [bool_state] :=
  match ir with
    | TimerInterrupt => (true,(None,false_ic))
    | DiskInterrupt => (false,(None,false_ic))
    | DefaultInterrupt => (false,(None,false_ic))
  end.*)

Definition bad_preroutine (o : [T_out']) (v : [stateType])  :=
  if is_I_out_done o is Some ir then let v := unset_masks v in if ir is TimerInterrupt then update_re_sch v true else v else v.

(*    update_bool_state v (or_bool_state (get_bool_state (unset_masks v)) (bad_to_bs ir)) else v.*)


Definition model_bad : Proc T_in T_out' := @loop_sta stateType initial_state T_in T_out' T' (state_step bad_preroutine id) def my_process_pool_bad f_si.

Definition Tsum' := ([T_in] + [T_out'])%type.

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

Definition seqtype' := seq Tsum'.
Eval cbv in T_out'.
(*traces for bad model*) 
Definition no_dI' : seqtype' :=   [::pub_get';                                     tI';pub_get';tI_no';tI_yes';sch_high;pr_nop'(*nop*);tI';pr_nop';tI_no';tI_yes';sch_low;pub_get'].
Definition with_dI' : seqtype' := [::pub_get';dI';pub_get';dI_no';dI_yes';pub_get';tI';pub_get';tI_no';tI_yes';sch_high;pr_sys'(*sys*);tI';pr_nop';tI_no';tI_yes';sch_low;pub_get'].
(*Definition with_dI' : seqtype' := [::tI';tI_no';tI_yes';sch_low;pub_get';dI';dI_no';dI_yes';pub_get';tI';tI_no';tI_yes';sch_high;pr_sys'(*sys*);pr_nop';tI';tI_no';tI_yes';pub_get'].*)

(*Definition output_rel' := eqpair (eqmaybe (publicRel TPublicOutput)) (eqpair (eqmaybe (semiprivateRel TTypeSyscall)) (eqmaybe (semiprivateRel THandlerOutput))).*)
(*Definition output_rel := eqmaybe (eqsum_R (publicRel TPublicOutput) (semiprivateRel TTypeSyscall)).*)

Ltac rewr := rewrite /model_bad /loop_sta /my_process_pool_bad /process_pool /my_f_initial /low_p /my_f_coopt /alternate_generic /alternate_generic2 /high_p /f_si /tI_o /I_handler /f_proj /scheduler /low_out.

Ltac lsolv := try solve [ reduce_tac;reduce_tac | reduce_tac;try solve [reduce_once | econ];simpl;first (reduce_tac;reduce_tac)];simpl.
Ltac reduce_tac2 :=
  (try rewr);
   (repeat
      reduce_once);(try swi_instans); rewrite ?eqxx /= /xor /=.


(* Concrete handler pids, so `reduce_state` never has to reduce TInterrupt's
   deriving-generated equality (index ir all_interrupts) — which is flaky under
   simpl/cbn. reflexivity (full conversion) discharges these fine. *)
(*Lemma I_handler_pid_timer   : I_handler_pid TimerInterrupt   = 0. Proof. reflexivity. Qed.
Lemma I_handler_pid_disk    : I_handler_pid DiskInterrupt    = 1. Proof. reflexivity. Qed.
Lemma I_handler_pid_default : I_handler_pid DefaultInterrupt = 2. Proof. reflexivity. Qed.*)

(* Unfolding lemmas: since we hide these below with `Opaque`, `unfold`/`simpl` no
   longer expose their bodies. Use `rewrite f_I_eq` (etc.) to unfold on demand. Each
   RHS is the definition's own body, captured with `cbv delta`, so nothing is copied
   by hand and the lemmas stay in sync with the definitions automatically. Stated
   here while the constants are still transparent, so `reflexivity` closes them. *)
Lemma f_I_eq : state_step = ltac:(let x := eval cbv delta [state_step] in state_step in exact x).
Proof. reflexivity. Qed.
Lemma f_si_eq : f_si = ltac:(let x := eval cbv delta [f_si] in f_si in exact x).
Proof. reflexivity. Qed.
Lemma initial_state_bad_eq :
  initial_state = ltac:(let x := eval cbv delta [initial_state] in initial_state in exact x).
Proof. reflexivity. Qed.
Lemma def_eq : def = ltac:(let x := eval cbv delta [def] in def in exact x).
Proof. reflexivity. Qed.
Lemma f_proj_eq : f_proj = ltac:(let x := eval cbv delta [f_proj] in f_proj in exact x).
Proof. reflexivity. Qed.

(* Collapse a tower of state getters/updaters into the concrete value it computes.
   Unfolds the base (initial_state_bad is Opaque) via its eq-lemma, replaces the
   handler-pid indices with their literals, delta-reduces only the state layer with
   cbv (so no eqType/other constants get dragged in), and finishes booleans/nats
   with simpl. Over a concrete base this yields a ground tuple; over an abstract
   state v it collapses to a tuple of expressions in v's fields. *)
(*Ltac reduce_state :=
  rewrite ?initial_state_bad_eq
          (*?I_handler_pid_timer ?I_handler_pid_disk ?I_handler_pid_default*);
  cbv [ state_step step0 step1 step2 step3 step4 step5 step_left step_right (*maybe_initiate_prev_pid maybe_initiate_scheduler maybe_initiate_handler*) get_pids get_bool_state get_cur_pid get_prev_pid get_re_sch get_ic
        get_I_bits get_I_bits' get_pending' get_mask' get_I_pending get_I_mask
        update_pids update_bool_state update_cur_pid update_prev_pid update_re_sch
        update_ic update_I_bits update_I_bits' update_I_pending update_I_mask
        or_I_bits or_ic or_bool_state
        set_masks unset_masks all_interrupts save_cur_to_prev is_user_pid
        (*default_on_ic*) false_ic false_I_bits initial_pid (*check_handlers initiate_handler initiate_scheduler*)
        compute_next_pid inspect_output
        foldr fst snd ];
  simpl.*)


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

(*Definition good_ic := ((false,((false,false),(false,false))).*)

(*Definition initial_state_good : [stateType] := ((initial_pid,None),(false,good_ic)).*)

Definition T'_good := Times (Option THandlerOutput) Bool.

Definition to_T'_good (o : [T_out']) : [T'_good] :=
  let b := if tI_out o is Some (Notify) then true else false in
  let o' := if dI_out o is Some (o') then Some o' else None in
  (o',b).

Definition my_f_I_good (n : nat) :=
  match n with
  | 0 => Unit (*tI*)
  | 1 => Unit (*dI*)
  | 2 => Unit (*defaultI*)
  | 3 => Empty (*scheduler*)         
  | 4 => THandlerOutput (*high*)
  | 5 => Unit (*low*)
  | _ => Unit (*padding*)           
  end.

Definition my_f_O_good (n : nat) :=
  match n with
  | 0 => THandlerOutput (*tI*)
  | 1 => THandlerOutput (*dI*)
  | 2 => THandlerOutput (*defaultI*)
  | 3 => Nat (*scheduler*)         
  | 4 => TTypeSyscall (*high*)
  | 5 => TPublicOutput (*low*)
  | _ => Unit (*padding*)           
  end.
                    
(*                            if n == 0 then Unit else if n == 4 then THandlerOutput else if n < 3 then Bool else Unit.*)
(*Definition my_f_O_good := fun (n : nat) => if n == 0 then THandlerOutput else if n == 3 then Nat else if n == 4 then TTypeSyscall else if n == 5 then TPublicOutput else Times THandlerOutput Bool.*)



(*We extend the input to schedulers so we can distinguish if the latest output was Notify by timer interrupt.
 This will feed their counter.
 true = from finishing timer interrupt, reset counter
 false = output pulse, decrement counter*)
Definition f_proj_good (i : [T'_good]) : forall n, [Option (my_f_I_good n)].
  simpl. rewrite /my_f_I_good. intros.
  case: n. exact None. (*timer interrupt handler does not need any information*)
  case. exact None.
  case. exact None.
  case. exact None. (*scheduler receives nothing*)
  case. exact (fst i). (*high process receives dI outut*)
  case. exact None. (*low process receives nothing*)
  move=>_. exact None.
Defined.  
(*other interrupts receive bool, true -> timer interrupt just finished, set count = 2, false -> decrement counter*)


Definition good_handler_type := Proc Bool (Times THandlerOutput Bool).
Definition default_on_ic : [ic] := ((true,false),((false,false),(false,false))). (*pending set for default*)
Definition mask_most : [ic] := ((false,true),((false,true),(false,false))). (*mask set for everything but timer interrupt*)

(*n = time slice*)
(*We assume that when the running handler is stopped by the timer, it has finished its work.
 Enforced by allowing time slice of 2.
 The two units are consumed by disk interrupt or default interrupt, in that order, if either or both their pending bits are set.
 If the timer interrupt runs again before either of the two other handlers then after completing the time slice will again be 2.
 All handlers take 2 units of time to complete, so by enforcing a time slice equal to length of a handler we never stop handlers mid execution.
 Assuming all handlers take the same amount of time and that we don't interrupt mid handling, are simplifying assumptions.
 *)
Definition good_I_handler (n : nat) : good_handler_type.
  eapply map. exact id.
  2: eapply sta.
  instantiate (2:= Nat).
  instantiate (1:= THandlerOutput).
  exact (fun o => if o.1 != 0 then (o.2,false) else (o.2,true)).
  exact (fun b n' => if b then n else n'.-1).
  exact (fun o n' => n').
  exact n.
  eapply map.
  instantiate (1:= Unit). exact (fun i => tt). exact id.
  apply I_handler.
Defined.

(*Definition time_slice := 3. *)
Definition good_tI_handler : handler_type := I_handler.
Definition good_dI_handler : handler_type := I_handler.
Definition good_default_handler : handler_type := I_handler.

Definition unit_proc : Proc Unit Unit.
  apply out. exact tt.
Defined.


Definition my_good_procs : forall n, Proc (@my_f_I_good n) (my_f_O_good n).
  case. apply good_tI_handler.
  case. apply good_dI_handler.
  case. apply good_default_handler.
  case. apply scheduler.
  case. apply high_p.
  case. apply low_p.
  elim. apply unit_proc.
  intros. apply unit_proc.
Defined.

Definition my_process_pool_good := @process_pool 5 my_f_coopt my_f_initial my_f_I_good my_f_O_good T'_good f_proj_good my_f_pid my_good_procs.

Definition def_good : [ T_out' ]  := (None,(None,(None,(None,(None,None))))).

(*Definition is_I_out_good (i : [T_out']) : [T'_good].
  case: i. move=>_.
  case. move=>_. 
  case. move=>_.
  simpl.
  case. case. case=>h. intros. exact (Some (h,false)).
  case. case. case=>h. intros. exact (Some (h,false)).
  case. case=>h. intros. exact (Some (h,true)). exact None.
Defined.*)

Definition f_si_good (si : [Times stateType (Sum T_in T_out')]) : [Option (Times cur_pid T'_good)] :=
  if si.2 is inr o then Some (get_cur_pid si.1, to_T'_good o) else None.

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

Definition compute_bool_state (b : [Bool]) : [bool_state] := (false,(None,((~~b,b),((false,b),(false,false))))).
Definition timer_bool_state : [bool_state] := (true,(None,((true,false),((false,false),(false,true))))).
(*Definition good_check_handlers (o : [T_out']) (v : [stateType])  :=
  if tI_out o is Some Notify then
    unset_masks v else v.*)



(*Definition good_check_handlers (o : [T_out']) : [stateType] ->  [stateType]  := ((good_check_other_handlers o) \o (good_check_tI o)).*)

(*Definition good_to_bs (ir : [TInterrupt]) (b : [Bool]) : [bool_state] :=
  (*  let ic := ((true,timeslice_done),((false,timeslice_done),(false,~~timeslice_done))) in*)
  let ic := ((true,false),((false,false),(true,false))) in
(*  let ic := ((true,ir_done),(((false,ir_done)),(false,~~ir_done))) in (*~~b ensures tI is masked during the time slice, this prevents infering from toggling tI mask that defaultI/diskI handler has run (which toggles all masks. So in essence, the secret handlers may run, this sets the mask of tI, if we are not finished, e.g. b = false, then we mask again. If we are done, b = true, we don't mess with the unset tI mask*)
  (*We need ir = dI to ensure that it only runs once, which ensures that defaultI runs as the last one, this allows the termination signal to be public because the defaultI may output it*)*)
  match ir with
    | TimerInterrupt => (true,(init_ir_count,((false,false),((false,false),(false,true)))))
    | DiskInterrupt => (false,(c,ic))
  | DefaultInterrupt => (false,(c,ic))
  end.*)

Definition initial_state_good : [stateType] := ((initial_pid,None),(false,(Some 0,mask_most))).

Definition unset_handler_masks (o : [T_out']) (v : [stateType])  :=
  match is_I_out_done o with
  | Some ir => unset_masks_sans v
  | _ => v                                                                   
  end.

Definition check_ir_count (o : [T_out']) (v : [stateType]) : [stateType] :=
  if tI_out o is Some Notify then update_ir_count (unset_masks_sans (set_tI v)) (Some 4)
  else
    match (get_ir_count v) with
    | Some n.+2 => update_ir_count v (Some n.+1)
    | Some 1 => update_ir_count (set_otherIs (unset_tI v)) (Some 0)                           
    | Some 0 | None => v
    end.

(*this is composed with the finial step3 function, ensuring that the state space we need to reason about has the bool_coding constraints, i.e. defaultInterrupt pending will be true*)
Definition bool_coding v := (update_re_sch (update_I_mask (update_I_pending v DefaultInterrupt true) DefaultInterrupt (get_I_mask v DiskInterrupt)) true).

Definition good_prereoutine (o : [T_out']) : [stateType] -> [stateType] := (check_ir_count o) \o (unset_handler_masks o) .

Definition model_good := @loop_sta stateType initial_state_good T_in T_out' T'_good (state_step good_prereoutine bool_coding) def_good my_process_pool_good f_si_good.


Definition tI_no'g : Tsum' :=  inr (tI_o (Nothing)).
Definition tI_yes'g : Tsum' :=  inr (tI_o (Notify)).

(*Definition default_and_masked_ic := or_bool_state (false, default_on_ic) (false, mask_most).*)

Definition dI_no'g : Tsum' :=  inr (dI_o (Nothing)).
Definition dI_yes'g : Tsum' :=  inr (dI_o (Notify)).
Definition dI_terminate'g : Tsum' :=  inr (dI_o (Notify)).

                                     
Definition defaultI_no'g : Tsum' :=  inr (defaultI_o (Nothing)).
Definition defaultI_yes'g : Tsum' :=  inr (defaultI_o (Notify)).
Definition defaultI_terminate'g : Tsum' :=  inr (defaultI_o (Notify)).

Definition good_no_dI' : seqtype' :=   [::pub_get';                      tI';pub_get';tI_no'g;tI_yes'g;defaultI_no'g;defaultI_yes'g;defaultI_no'g;defaultI_terminate'g;sch_high;pr_nop'(*nop*);tI';pr_nop';tI_no'g;tI_yes'g;defaultI_no'g;defaultI_yes'g;defaultI_no'g;defaultI_terminate'g;sch_low;pub_get'].
Definition good_with_dI' : seqtype' := [::pub_get';dI';pub_get';pub_get';tI';pub_get';tI_no'g;tI_yes'g;dI_no'g      ;dI_yes'g      ;defaultI_no'g;defaultI_terminate'g;sch_high;pr_sys'(*sys*);tI';pr_nop';tI_no'g;tI_yes'g;defaultI_no'g;defaultI_yes'g;defaultI_no'g;defaultI_terminate'g;sch_low;pub_get'].


Ltac rewr ::= rewrite /model_bad /loop_sta /my_process_pool_bad /process_pool /my_f_initial /low_p /my_f_coopt /alternate_generic /alternate_generic2 /high_p /f_si /tI_o /I_handler /f_proj /scheduler /low_out /model_good /my_process_pool_good /f_si_good /to_T'_good /f_proj_good /good_default_handler /good_tI_handler /good_dI_handler /good_I_handler.

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

Definition ir_dis (l : level) (ir : [TInterrupt]) := ir = DiskInterrupt /\ l = \bot.
Definition TInterrupt_rel : myrel [TInterrupt].
  refine (@MyRel _
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


Definition in_rel : myrel [T_in] := TInterrupt_rel.

Definition out_rel : myrel [T_out'] := eqpair (eqmaybe (publicRel _))
                                          (eqpair (eqmaybe (semiprivateRel _))
                                             (eqpair (eqmaybe (publicRel _))
                                                (eqpair (eqmaybe_top ((semiprivateRel _)))
                                                   (eqpair (eqmaybe_top (semiprivateRel _))
                                                      (eqmaybe (publicRel _)))))).

Lemma Trace_imp : forall (A B : Ty) (p : Proc A B) (s : seq ([A] + [B])) l (BRel BRel' : myrel [B]), (forall x y, rel BRel l x y -> rel BRel' l x y) -> Trace BRel l s p -> Trace BRel' l s p.
Proof.  
  intros.
  elim : H0 H;ssa.
  econ. eauto. eauto.
  econ;eauto.
Qed.

Lemma helper_trace' : Trace (publicRel _) false [::pub_get';pub_get'] model_bad.
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

Lemma helper_trace : Trace out_rel false [::pub_get';pub_get'] model_bad.
Proof.
  eapply Trace_imp. 2:eapply helper_trace'.
  intros. simpl in H. subst. auto.
Qed.  


(* Part B (see plan): keep the large *data* leaves folded during this proof so
   coq-lsp does not serialize their unfolded bodies while `match_dd` inverts the
   reduction. These are only carried by map/sta nodes, never pattern-matched by the
   inversion, so hiding them cannot block `match_dd`. NOTE: my_f_I/my_f_O (type
   indices) and my_f_initial (feeds the swi bool that reduce_swiO/swiO2 must see
   concretely) are deliberately NOT hidden. Scoped to this lemma; restored below. *)
Opaque state_step f_si initial_state def f_proj.

Lemma model_bad_not_NI : ~ NI in_rel out_rel model_bad.
Proof.
  intro. rewrite /NI in H. move: (H false). clear H.
  rewrite /NI_l. case=>_ [] + _. intros.
  move: helper_trace.
  move/a. move/(_ (DiskInterrupt) 0). simpl.
  have: ir_dis false DiskInterrupt. ssa.
  move=>aa. move/(_ aa).
  move=>Htr. clear a aa.
  inv Htr;clear Htr;match_dd. 
  rewrite f_si_eq /= in x. clear x.
  inv H3;clear H3;match_dd. ssa.
  inv H5;clear H5;match_dd.
  move: H9. clear. simpl. ssa.
Qed.

Transparent f_si initial_state def f_proj.

Lemma eqsum_L_llrr l i i' : rel (eqsum_L in_rel out_rel) l i i' -> is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'.
Proof.
  intros. destruct i. destruct i'. ssa.
  exfalso. ssa. destruct i'. ssa. ssa.
Qed.

Lemma eqsum_llrr  (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B])  l i i' : rel (eqsum ARel BRel) l i i' -> is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'.
Proof.
  intros. destruct i. destruct i'. ssa.
  exfalso. ssa. destruct i'. ssa. ssa.
Qed.

Lemma eqsum_split (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l i0 i1 : rel (eqsum ARel BRel) l i0 i1 -> (exists i0' i1', (i0 = inl i0' /\ i1 = inl i1' /\ rel ARel l i0' i1')) \/
                                                                                                              exists i0' i1', (i0 = inr i0' /\ i1 = inr i1' /\ rel BRel l i0' i1').
Proof.
  intros. apply eqsum_llrr in H as H'. destruct H'.
  destruct H0. destruct i0. destruct i1.
  left. exists i. exists i0. ssa.
  ssa. ssa. destruct i0. ssa.
  destruct i1. ssa.
  right. exists i. exists i0. ssa.
Qed.

Lemma semiprivate_not_bot : forall (A : Ty) l (x y : [A]), l <> \bot -> x = y -> rel (semiprivateRel _) l x y.
Proof.
ssa.
Qed.

Lemma semiprivate_not_bot' : forall (A : Ty) l (x y : [A]), l <> \bot -> rel (semiprivateRel _) l x y -> x = y.
Proof.
ssa. de H0.
Qed.

Lemma eqmaybe_semiprivate_not_bot' : forall (A : Ty) l (x y : [Option A]), l <> \bot -> rel (eqmaybe (semiprivateRel _)) l x y -> x = y.
Proof.
ssa. de x. de y. de H0. subst. done. de y.
Qed.

Lemma eqmaybe_public_not_bot : forall (A : Ty) l (x y : [Option A]), l <> \bot -> rel (eqmaybe (publicRel _)) l x y -> x = y.
Proof.
ssa. de x. de y. subst. done. de y.
Qed.

Lemma eqmaybe_semiprivate_not_bot : forall (A : Ty) l (x y : [Option A]), l <> \bot -> rel (eqmaybe_top (semiprivateRel _)) l x y -> x = y.
Proof.
ssa. de x. de y. de H0. subst. done. de y.
Qed.

Lemma eqmaybe_semiprivate_bot : forall (A : Ty) (x y : [Option A]), rel (eqmaybe_top (semiprivateRel _)) \bot x y.
Proof.
  ssa. de x. de y. de y.
Qed.

Lemma semiprivate_bot : forall (A : Ty) (x y : [A]), rel ((semiprivateRel _)) \bot x y.
Proof.
  ssa.
Qed.

Hint Resolve semiprivate_bot.
(*
  H2 : rel (eqmaybe (semiprivateRel TTypeSyscall)) l i1 i6
  H3 : rel (eqmaybe (publicRel Nat)) l i2 i7
  H4 : rel (eqmaybe (publicRel I_output_type)) l i3 i8
  H5 : rel (eqmaybe_top (semiprivateRel I_output_type)) l i4 i9
  H6 : rel (eqmaybe_top (semiprivateRel I_output_type)) l i5 i10
 *)

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
  move=>/eqmaybe_semiprivate_not_bot'=>->//.
  move=>/eqmaybe_public_not_bot=>->//.
  move/rel_eqmaybe_top.
  case.
  move=>[x0][y0][]->[]-> /semiprivate_not_bot' ->//.
  move=>/eqmaybe_semiprivate_not_bot=>->//.
  move=>/eqmaybe_public_not_bot=>->//.
  case. ssa.
  case. ssa.
  move=>[]->->.
  move=>/eqmaybe_semiprivate_not_bot=>->//.
  move=>/eqmaybe_public_not_bot=>->//.  
Qed.



Lemma falseRel_aware : forall l, aware falseRel true l.
Proof.
intros. rewrite /aware. intros. ssa. subst. simpl. intro. ssa.
Qed.

(*Definition lt_dis (nP : nat -> Prop) (l : level) (n : nat) := nP n /\ l = \bot.

Definition natLTRel (nP : nat -> Prop) : myrel ([Nat]).
  refine (@MyRel _
            (lt_dis nP)
            (fun l n1 n2 => n1 = n2 \/ (lt_dis nP l n1) /\ (lt_dis nP l n2))
            _
            _
            _
            _).
  ssa. con. intro. ssa. intro. ssa. de H.
  intro. ssa. de H. subst. de H0. de H0. subst.
  move: H H1. rewrite /lt_dis. ssa.
  ssa. de H0. move: H0 H1. rewrite /lt_dis. ssa. subst.
  rewrite /order lex0 in H. move/eqP : H=>->. ssa.
  ssa. move: H0. rewrite /lt_dis. ssa. subst.
  rewrite /order lex0 in H. move/eqP : H=>->. done.
  ssa. move: H. rewrite /lt_dis. ssa. subst.
  con. intros. ssa. ssa. de H0. subst. done.
Defined.*)

Definition pids_rel : myrel [pids] := eqpair (eqsum (semiprivateRel _) (publicRel _)) (publicRel _).
Definition hidden_pair : myrel [I_bits] := eqpair (semiprivateRel _) (semiprivateRel _).
Definition public_pair : myrel [I_bits] := eqpair (publicRel _) (publicRel _).
Definition ic_rel : myrel [ic] := eqpair hidden_pair (eqpair hidden_pair public_pair).
Definition bool_state_rel : myrel [bool_state] := eqpair (publicRel _) (eqpair (publicRel _) ic_rel).
Definition stateType_rel : myrel [stateType] := eqpair pids_rel bool_state_rel.



Lemma stateType_rel_not_bot : forall i i' l, l <> \bot -> rel stateType_rel l i i' -> i = i'.
Proof.
  intros.
  move:H0.
  move/rel_eqpair=> [] /rel_eqpair[] + + /rel_eqpair [] + /rel_eqpair [] + /rel_eqpair [] /rel_eqpair [] + + /rel_eqpair[] /rel_eqpair[] + + /rel_eqpair [] + +.
  move: i=>[[a0 a1]] [b [b0 [[b1 b2 [[b3 b4 [b5 b6]]]]]]].
  move: i'=>[[a0' a1']] [b' [b0' [[b1' b2' [[b3' b4' [b5' b6']]]]]]].  
  rewrite !pair_rewr. 
  move=> /eqsum_split Hsplit.
  move=>/publicRel_eq -> /publicRel_eq -> /publicRel_eq -> // /semiprivate_not_bot' -> // /semiprivate_not_bot' -> // /semiprivate_not_bot' /publicRel_eq -> // /semiprivate_not_bot' -> // /publicRel_eq -> /publicRel_eq ->.
  case: Hsplit.
  move=>[x][y][]->[]->/semiprivate_not_bot' ->//.
  move=>[x][y][]->[]-> /publicRel_eq ->//.  
Qed.


Transparent state_step f_si initial_state def f_proj.
(*Lemma state_step_inl i v f f' : state_step f f' (inl i) v = update_I_pending v i true.
Proof. reflexivity. Qed.*)

Lemma in_rel_eq i i0 l : rel in_rel l i i0 -> i = i0.
Proof.
  ssa. de H. move: H H0. rewrite /ir_dis. ssa. subst. done.
Qed.


Lemma fv_NI_comp : forall (I V: Ty) (IRel : myrel [I]) (VRel : myrel [V]) (f f' : [I]  -> [V] ->  [V]),
    fv_NI IRel VRel VRel f -> fv_NI IRel VRel VRel f' -> fv_NI IRel VRel VRel (fun i => (f' i) \o (f i)).
Proof.
intros. move: H H0. rewrite /fv_NI. ssa.
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

Lemma model_good_NI : NI in_rel out_rel model_good.
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

  rewrite /unset_handler_masks.

  mrw. intros.
  destruct (eqVneq l \bot).
  2: {  apply out_rel_not_bot in H. 2:apply/eqP=>//. subst.
        apply stateType_rel_not_bot in H0. 2:apply/eqP=>//. subst. eauto. }
  subst.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H=> /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] + /rel_eqpair[] + +.
  move: i=>[a[] b[] c[] d[] e f].
  move: i'=>[a'[] b'[] c'[] d'[] e' f']. 
  rewrite !pair_rewr /is_sch_out.
 
  case/rel_eqmaybe_top.
  move=>[]x []y []-> []->// Hdef.

  case/rel_eqmaybe_top.
  move=>[]x0 []y0 []-> []->// Hdisk.

  case/rel_eqmaybe2.
  move=>[]x1 []y1 []-> []->// /publicRel_eq ->//.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y1. 
  case:x0 Hdisk. rewrite /default_I_out.
  case:x Hdef.
  case:y0. 
  case:y. ssa. ssa. 
  move=> _ _. ssa.
  case:y0.
  case:y. ssa. ssa. ssa.
  case:y0. case:y Hdef. ssa. ssa. ssa. ssa.
  case=>->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:x0 Hdisk.
  case:x Hdef.
  move=>_ _.
  case:y0.
  case:y. ssa. ssa. ssa.
  case:y0. case:y. ssa. ssa. ssa.
  case:y0. case:y Hdef. ssa. ssa. ssa.

  case.
  move=>[x0][]->[]-> _.

  case/rel_eqmaybe2.
  move=>[]x1 []y1 []-> []->// /publicRel_eq ->.

  rewrite /is_I_out_done /tI_out.
  case:y1. rewrite /dI_out.
  case:x0. rewrite /default_I_out.
  case:x Hdef.
  case:y. ssa. ssa. case:y. ssa. ssa.
  rewrite /default_I_out.
  case:y Hdef. ssa. ssa. ssa.
  case=>->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:x0.
  case:x Hdef.
  case:y. ssa. ssa. case:y. ssa. ssa.
  case:y Hdef. ssa. ssa.

  case.
  move=>[] x1 []->[]->_.
  case/rel_eqmaybe2.
  move=>[]x2 []y2 []-> []->// /publicRel_eq ->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.

  case:y2.
  case:x Hdef.
  case:x1.
  case:y. ssa. ssa. ssa.
  case:x1. case:y. ssa. ssa. ssa. ssa.
  move=>[]->->.

  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  
  case:x Hdef.
  case:x1. case:y. ssa. ssa. ssa.
  case:x1. case:y. ssa. ssa. ssa.
  move=>[]->->.

  case/rel_eqmaybe2.
  move=>[]x'[]y'[]->[]->/publicRel_eq->.

  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y'. case:x Hdef. case:y. ssa. ssa.
  case:y. ssa. ssa. ssa.
  move=>[]->->.

  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:x Hdef.
  case:y. ssa. ssa.
  move=>_. case:y. ssa. ssa.
  case.
  move=>[x][]->[]->_.

  case/rel_eqmaybe_top.
  move=>[]x'[]y'[]->[]-> _.

  case/rel_eqmaybe2.
  move=>[]x0'[]y0'[]->[]->/publicRel_eq->.  

  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y0'. case:x.
  case:x'. case:y'. ssa. ssa.
  case:y'. ssa. ssa.
  case:x'. case:y'. ssa. ssa.
  case:y'. ssa. ssa. ssa.
  move=>[]->->.

  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:x'.
  case:x.
  case:y'. ssa. ssa. case:y'. ssa. ssa. case:y'. ssa. ssa.

  case.
  move=>[]x0[]->_.
  case/rel_eqmaybe2.
  move=>[]x0'[]y0'[]->[]->/publicRel_eq->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y0'. case:x0.
  case:x. case: e'.
  case. ssa. ssa. ssa.
  case:e'. case. ssa. ssa. ssa.
  case:e'. case. ssa. ssa. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:x0. case:x. case:e'.
  case. ssa. ssa. ssa.
  case:e'. case. ssa. ssa. ssa.
  case:e'. case. ssa. ssa. ssa.
  case.
  move=>[]y'[]->[]->_.
  case/rel_eqmaybe2.
  move=>[]x0'[]y0'[]->[]->/publicRel_eq->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.  
  case:y0'.
  case:x. case:y'. ssa. ssa.
  case:y'. ssa. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.  
  case:x. case:y'. ssa. ssa.
  case:y'. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.  
  case/rel_eqmaybe2.
  move=>[]x0'[]y0'[]->[]->/publicRel_eq->.  
  case:y0'. case:x. ssa. ssa. ssa.
  move=>[]->->.
  case:x. ssa. ssa.
  case. move=>[]y'[]->[]->_.
  case/rel_eqmaybe_top.
  move=>[]x0'[]y0'[]->[]->_.

  case/rel_eqmaybe2.
  move=>[]x1'[]y1'[]->[]->_.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.  
  case:x1'. case:x0'.
  case:y1'. case:y0'.
  case:y'. ssa. ssa. ssa. ssa.
  case:y1'. case:y0'.
  case:y'. ssa. ssa. ssa. ssa.
  case:y1'. case:y0'. case:y'. ssa. ssa. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.  
  case:x0'. case:y0'. case:y'. ssa. ssa. ssa.
  case:y0'. case:y'. ssa. ssa. ssa.

  case.
  move=>[]x []->[]->_.
  case/rel_eqmaybe2.
  move=>[]x1'[]y1'[]->[]->_.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.  
  case:x1'. case:x. case:y1'. case:y'. ssa. ssa. ssa.
  case:y1'. case:y'. ssa. ssa. ssa.
  case:y1'. case:y'. ssa. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.  
  case:x. case:y'. ssa. ssa.
  case:y'. ssa. ssa.
  case.
  move=>[]x []->[]->_.
  case/rel_eqmaybe2.
  move=>[]x1'[]y1'[]->[]->/publicRel_eq ->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.  
  case:y1'. case:x. case:y'. ssa. ssa. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:x. case:y'. ssa. ssa. ssa.
  move=>[]->->.
  case/rel_eqmaybe2.
  move=>[]x1'[]y1'[]->[]->/publicRel_eq ->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y1'.
  case:y'. ssa. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y'. ssa. ssa.
  move=>[]->->.
  case/rel_eqmaybe_top.
  move=>[]x1'[]y1'[]->[]->_.
  case/rel_eqmaybe2.
  move=>[]x2'[]y2'[]->[]->/publicRel_eq ->.  
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y2'. case:x1'. case:y1'. ssa. ssa.
  case:y1'. ssa. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:x1'. case:y1'. ssa. ssa.
  case:y1'. ssa. ssa.

  case.
  move=>[]x'[]->[]->_.
  case/rel_eqmaybe2.
  move=>[]x2'[]y2'[]->[]->/publicRel_eq ->.   
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y2'. case:x'. ssa. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:x'. ssa. ssa.

  case.
  move=>[]x'[]->[]->_.
  case/rel_eqmaybe2.
  move=>[]x2'[]y2'[]->[]->/publicRel_eq ->.   
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y2'. case:x'. ssa. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:x'. ssa. ssa.
  move=>[]->->.
  case/rel_eqmaybe2.
  move=>[]x1'[]y1'[]->[]->/publicRel_eq ->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  case:y1'. ssa. ssa.
  move=>[]->->.
  rewrite /is_I_out_done /tI_out /dI_out /default_I_out.
  ssa.


  mrw. intros.
  destruct (eqVneq l \bot).
  2: {  apply out_rel_not_bot in H. 2:apply/eqP=>//. subst.
        apply stateType_rel_not_bot in H0. 2:apply/eqP=>//. subst. eauto. }
  subst.  
  rewrite /check_ir_count.

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

(*  have:get_ir_count (update_re_sch (update_I_pending v DefaultInterrupt true) true)= get_ir_count v.  ssa.
  move=>->.
  have:get_ir_count (update_re_sch (update_I_pending v' DefaultInterrupt true) true)=get_ir_count v'. ssa.
  move=>->.*)
  
  have: get_ir_count v = get_ir_count v'.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move/publicRel_eq : H2=>->//.

  
  move=>->.

  destruct (tI_out i').
  destruct h.
  destruct (get_ir_count v').
  destruct n. ssa.
  destruct n. ssa. ssa. ssa. ssa.
  destruct (get_ir_count v').
  destruct n. ssa. destruct n. ssa. ssa. ssa.

  mrw. intros.
  clear H.

  mrw. intros.
  destruct (eqVneq l \bot).
  2: {  
        apply stateType_rel_not_bot in H0. 2:apply/eqP=>//. subst. eauto. }
  subst.

  rewrite /comp /bool_coding /initiate_next.

  rewrite !first_ready_update_re_sch.

  have: I_ready  (update_I_mask (update_I_pending v DefaultInterrupt true) DefaultInterrupt (get_I_mask v DiskInterrupt)) TimerInterrupt =
          I_ready (update_I_mask (update_I_pending v' DefaultInterrupt true) DefaultInterrupt (get_I_mask v' DiskInterrupt)) TimerInterrupt. 


  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H6. move/rel_eqpair=>[]. rewrite !pair_rewr. move=>/publicRel_eq->/publicRel_eq->. ssa.
  
  move/ready_cases2P. rewrite /ready_cases2.

  move=>[[]Hready[]Hready'[]Hfirst Hfirst'|[]Hready[]Hready'[]Haux Haux'].
  rewrite Hfirst Hfirst'. admit.

  move:Haux Haux'.
  rewrite /ready_aux2.
  move=>[[]HreadyD Hfirst|].
  move=>[[]HreadyD' Hfirst'|[]].
  rewrite Hfirst Hfirst'. admit.
  move=>[]HreadyD'[]HreadyDef' Hfirst'.
  rewrite Hfirst Hfirst'. admit.
  move=>[]HreadyD'[]HreadyDef' Hfirst'.
  rewrite Hfirst Hfirst'. exfalso. admit.

  move=>[[]HreadyD[]HreadyDef Hfirst|].
  move=>[[]HreadyD' Hfirst'|].
  rewrite Hfirst Hfirst'. admit.

  move=>[[]HreadyD'[]HreadyDef' Hfirst'|].
  rewrite Hfirst Hfirst'. admit.

  move=>[]HreadyD'[]HreadyDef' Hfirst'.
  rewrite Hfirst Hfirst'. exfalso. admit.
  



  
  move: (ready_casesP v v').
  rewrite /ready_cases.
  have: is_I_out_done i' = 
  move=>+[][]. move=>++->.
  move=>++[][]. move=>+++->.
  admit.
  move=>->+[]//.
  move=>->+[]//;ssa.
  move=>+[]+[]+->.
  move=>->+[]//;ssa.

  move: v H0 Heq Ht Ht' => [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].    

  rewrite /initiate_handler. simpl. 
  
  move: H=> /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] + /rel_eqpair[] + +.
  move: i=>[a[] b[] c[] d[] e f].
  move: i'=>[a'[] b'[] c'[] d'[] e' f']. 
  rewrite !pair_rewr /is_sch_out.
 
  case/rel_eqmaybe_top.
  move=>[]x []y []-> []->// Hdef.

  case/rel_eqmaybe_top.
  move=>[]x0 []y0 []-> []->// Hdisk.

  case/rel_eqmaybe2.
  move=>[]x1 []y1 []-> []-> /publicRel_eq ->// .
  destruct (first_ready (cur, prev, (re_sch, (ir_count, (def_pending, def_mask, (disk_pending, disk_mask, (timer_pending, timer_mask))))))) eqn:Heqn.
  rewrite Heqn.

  have: i = TimerInterrupt -> first_ready (cur', prev', (re_sch', (ir_count', (def_pending', def_mask', (disk_pending', disk_mask', (timer_pending', timer_mask')))))) = Some i.
  intros. subst.
  move:Heqn.
  case/rel_eqpair2: H6. rewrite !pair_rewr. move=>/publicRel_eq -> /publicRel_eq ->.
  cbv.
  case:timer_pending'.
  case:timer_mask'.
  case:disk_pending H5.
  case:disk_mask.
  case:def_pending H3.
  case:def_mask H4. ssa. ssa. ssa. ssa.
  move=>_.
  case:def_pending H3.
  case:def_mask H4. ssa. ssa. ssa. ssa.
  case:disk_pending H5.
  case:disk_mask.
  case:def_pending H3.
  case:def_mask H4. ssa. ssa. ssa. ssa.
  case:def_pending H3.
  case:def_mask H4. ssa. ssa. ssa.
  move=>Heq.
  destruct i. simpl.
  
  case:disk_pending
  case_if;ssa.
  case_if. move: H. case_if.

  destruct (I_ready ((cur, prev, (re_sch, (ir_count, (def_pending, def_mask, (disk_pending, disk_mask, (timer_pending, timer_mask))))))) TimerInterrupt) eqn:Heqn.


  case/rel_eqmaybe2.
  have: first_ready (cur, prev, (re_sch, (ir_count, (def_pending, def_mask, (disk_pending, disk_mask, (timer_pending, timer_mask))))))
        =first_ready (cur, prev, (re_sch, (ir_count, (def_pending, def_mask, (disk_pending, disk_mask, (timer_pending, timer_mask)))))).
  cbv.
  move=>[]x1 []y1 []-> []->// Htim.

  rewrite /first_ready /ohead /I_ready /all_interrupts.

  
  


  

  rewrite /update_I_pending /update_I_bits /update_ic /update_ic_count /update_bool_state.
  rewrite !pair_rewr. ssa.

  ssa. ssa.
  apply/rel_eqpair2;con;try solve [ssa].

  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  rewrite !pair_rewr.    
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  rewrite !pair_rewr. eauto.
  case=>->->.
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  rewrite !pair_rewr.    
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.  
  rewrite !pair_rewr. eauto.

  (*step2*)
  apply fv_NI_comp.
  
  rewrite /step2.
  apply fv_NI_step_right.
  rewrite /check_handlers.

  mrw. intros.

  destruct (eqVneq l \bot).
  2: {  apply out_rel_not_bot in H. 2:apply/eqP=>//. subst.
        apply stateType_rel_not_bot in H0. 2:apply/eqP=>//. subst. eauto. }
  subst.

  move: v H0=> [[cur prev]] [re_sch] [ir_count] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [ir_count'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].  

  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[] H2 /rel_eqpair[]/rel_eqpair[H3 H4] /rel_eqpair[] H5 H6.
  rewrite !pair_rewr in H0 H1 H2 H3 H4 H5 H6.

  move: H=> /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + /rel_eqpair[] + +.
  move: i =>[a[] b[] c[] d[] e f]. 
  move: i'=>[a'[] b'[] c'[] d'[] e' f'].
  rewrite !pair_rewr.
 
  case/rel_eqmaybe2.
  move=>[]x []y []-> []->// /publicRel_eq ->.

  case/rel_eqmaybe2.
  move=>[]x' []y' []-> []->// Hsys.

  case/rel_eqmaybe2.
  move=>[]x'' []y'' []-> []->// /publicRel_eq ->.

  case/rel_eqmaybe_top.
  move=>[]x''' []y''' []-> [] ->// Hdef.

  case/rel_eqmaybe_top.
  move=>[]x'''' []y'''' []-> [] ->// Hdisk.

  case/rel_eqmaybe2.
  move=>[]x''''' []y''''' []-> [] ->// /publicRel_eq ->.    

  rewrite /is_I_out_done.

  rewrite /tI_out.
  case: y'''''.
  rewrite /dI_out.
  case: x'''' Hdisk.
  case: y''''.
  move=>Hdisk.
  rewrite /default_I_out.
  move: x''' y''' Hdef.
  move=>[] [].
  move=>Hdef.
  
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  rewrite !pair_rewr.    
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con;first ssa.
  rewrite !pair_rewr. eauto.

  move=>Hdef.
  
  apply/rel_eqpair2;con;first ssa.
  apply/rel_eqpair2;con.
  rewrite !pair_rewr. rewrite orbC /orb. eauto.
  rewrite !pair_rewr.
  apply/rel_eqpair2;con. 
  rewrite !pair_rewr. eauto.
  rewrite /get_I_pending /get_pending' /get_I_bits /get_I_bits' /get_ic /get_bool_state orbC /orb.

  rewrite !pair_rewr. 
    
  apply/rel_eqpair2;con.
  apply/rel_eqpair2;con.
  rewrite !pair_rewr. eauto.

  rewrite !pair_rewr. eauto.
  
  apply/rel_eqpair2;con.
  apply/rel_eqpair2;con. eauto.
  rewrite !pair_rewr. eauto.
  apply/rel_eqpair2;con. rewrite !pair_rewr orbC /orb.
  move/rel_eqpair2 : H6=>[]. eauto.

  rewrite !pair_rewr.
  rewrite /orb /get_ir_count /get_ic_count /get_bool_state !pair_rewr.
  
  apply/rel_eqpair2;con;eauto.  


  destruct i. exfalso;ssa.
  destruct i'. exfalso;ssa.
  apply rel_eqsum_L2' in H.
  clear H1. move: H0.
  move/rel_eqpair=>[H0] /rel_eqpair[H1] /rel_eqpair[]/rel_eqpair[H2 H3] /rel_eqpair[]/rel_eqpair[H4 H5] /rel_eqpair[] H6 H7.
  move: H0 H1 H2 H3 H4 H5 H6 H7.
  move: v=> [[cur prev]] [re_sch] [[def_pending def_mask]] [[disk_pending disk_mask]] [timer_pending timer_mask].
  move: v'=> [[cur' prev']] [re_sch'] [[def_pending' def_mask']] [[disk_pending' disk_mask']] [timer_pending' timer_mask'].
  rewrite !pair_rewr.
  move=> H0 H1 H2 H3 H4 H5 H6 H7.
  
  rewrite /state_step /step_on_output.

 have: rel stateType_rel l
    ((inspect_output good_to_bs i)
       (cur, prev, (re_sch, (def_pending, def_mask, (disk_pending, disk_mask, (timer_pending, timer_mask))))))
    ((inspect_output good_to_bs i0)
       (cur', prev', (re_sch', (def_pending', def_mask', (disk_pending', disk_mask', (timer_pending', timer_mask')))))).

 rewrite /inspect_output.

 have:   rel stateType_rel l
    ((check_scheduler i)
       (cur, prev, (re_sch, (def_pending, def_mask, (disk_pending, disk_mask, (timer_pending, timer_mask))))))
    (( check_scheduler i0)
       (cur', prev', (re_sch', (def_pending', def_mask', (disk_pending', disk_mask', (timer_pending', timer_mask')))))).


  


 
 rewrite /is_I_out_done. rewrite /tI_out. simpl.
 case: f=>a0.
 case: f'=>a1. move=>->//. ssa.
 case: f' a0=>//. ssa.
 move=> HtI_out.

 
 have: tI_out i = tI_out i0.
 move: H=> /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _ /rel_eqpair[] _.
 move: i=>[a[] b[] c[] d[] e f].
 move: i0=>[a'[] b'[] c'[] d'[] e' f']. 
 rewrite !pair_rewr.
 rewrite /is_I_out_done. rewrite /tI_out. simpl.
 case: f=>a0.
 case: f'=>a1. move=>->//. ssa.
 case: f' a0=>//. ssa.
 move=> HtI_out.

 rewrite /inspect_output.
 
 move/rel_eqmaybe2.
 case.
 move=>[] [h0 b0] [][h1 b1][]->[]->/=[]->->.
 case: h1.
 move=>HH.
 apply rel_eqmaybe2 in HH.
 Search _ (rel (eqmaybe _)).
 have: rel (publicRel (Times THandlerOutput Bool)) l f f'. ssa.
 clear HH => HH.
 move: f f' HH=> [f b0] [f' b0']=>/=.
 case=>->->.
 case: f'.

 rewrite /inspect_output /check_handlers /check_scheduler.
 rewrite /is_I_out_done.


  
  rew
  ssa. de v. de p. de s. de v'. de p. de s. de H0.
  rewrite /update_I_bits'.
  rewrite !pair_rewr.  
  apply/rel_eqpair2.
  simpl in H. destruct H. subst. eauto.
  have: state_step good_to_bs (inl i) = state_step good_to_bs (inl i). simpl. rewrite /state_step.
  Search _ (rel (eqsum_L _ _)).
  destruct i. destruct i0. destruct H. subst. ssa. ssa.
  left. ssa.
  move: H H3. rewrite /ir_dis. ssa. done. de i0. done. ssa.
  destruct i. ssa. destruct i'. ssa.
  apply rel_eqsum_L2' in H.
  apply out_rel_not_bot in H. subst. eauto. done.
  subst. eauto.










  

  mrw. intros. destruct i. 2:ssa.
  have: dis in_rel l i. ssa. clear H=>H.
  destruct (eqVneq l \bot). subst. ssa.
  ssa. de i. rewrite /ir_dis in H. ssa.

  eapply map_NI.

  4: eapply maybe_NI.
  mrw. intros. destruct i. destruct i'.
  rewrite !pair_rewr.
  apply rel_eqpair_R2' in H.
  destruct H. destruct H.
  apply eqsum_L_llrr in H0 as H0'.
  destruct H0'. destruct i0. destruct i2. ssa. ssa. ssa.
  destruct i0. ssa. destruct i2. ssa.
  apply rel_eqmaybe_false2.
  instantiate (1:= eqpair _ _).
  apply rel_eqpair2. rewrite !pair_rewr. con.
  instantiate (1:= publicRel _). (*changed from private to public*)
  clear H0 H1. Print stateType.

  destruct (eqVneq l \bot). subst. eauto.
  apply semiprivate_not_bot' in H. subst. eauto. apply/eqP. done.
  instantiate (1:= eqpair _ _).
  apply rel_eqpair2. rewrite !pair_rewr. con.
  instantiate (1:= eqmaybe_top (semiprivateRel _)).
  apply rel_eqsum_L2' in H0.
  clear H1.
  destruct (eqVneq l \bot). subst. apply eqmaybe_semiprivate_bot.

  apply  out_rel_not_bot in H0. subst. eauto. apply/eqP. done.
  clear H.
  apply rel_eqsum_L2' in H0.
  destruct (eqVneq l \bot). subst. eauto.
  apply  out_rel_not_bot in H0. subst. eauto. apply/eqP. done.
  destruct H. destruct i0. 2:ssa. destruct i2. 2:ssa. auto.
  mrw. intros.
  destruct i.
  apply dis_eqpair_R in H. destruct i0. 2:ssa.
  have: dis in_rel l i0. ssa. clear H=>H.
  rewrite !pair_rewr. done.
  mrw. intros.
  apply rel_eqsum_L2. eauto.

  apply par_NI.

  eapply map_NI. 
  4: eapply swi_NI.
  mrw. intros.
  move/rel_eqpair : H. case=>H0 H1.
  apply rel_eqpair_LR2. con.
  instantiate (1:= falseRel).
  


  5: { intros. left. apply falseRel_aware. move: H0. clear. ssa. de H0.
  5: eapply maybe_NI. eauto.
  2: { mrw. intros. move: H. instantiate (1:= publicRel _). simpl. de i. de i'. de i'. }
  mrw. ssa. 

  3: { mrw. intros. simpl in i,i'.
       move: H. instantiate (1:= publicRel _). instantiate (1:= publicRel _). ssa. de i. de i'. de i'. }
  mrw. intros.


  mrw. intros.
  destruct i. destruct i0.  destruct i'. destruct i3.
  rewrite !pair_rewr.
  move:H. move/rel_eqpair=>[] H0 /rel_eqpair [] H1.
  rewrite !pair_rewr in H0 H1. rewrite !pair_rewr.
  intros.
  instantiate (1:= eqpair _ _). apply rel_eqpair2.
  rewrite !pair_rewr. con.
  instantiate (1:= semiprivateRel _). move: H0. clear.
  intros. ssa. de H0. eauto. 2:eauto.
  mrw. intros. ssa.

  eapply swi_NI.
  
  
  Search _ (rel (eqsum_L _ _)).
  clear H1.

  apply rel_eqsum_L2' in H0.
  destruct (eqVneq l \bot). subst.
  apply eqmaybe_semiprivate_bot.
  apply semiprivate_not_bot' in H;eauto. subst.
  apply eqmaybe_semiprivate_not_bot.  
  ssa.
  de i0.
  ssa. de H. subst.
  Search _ (eqmaybe_false). (Some _)).
  Search _ (rel (eqpair_R _ _)).  
  4: eapply par_NI.

