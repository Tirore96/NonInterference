
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

Definition process_pool
  (n : nat)
  (f_coopt : nat -> bool)
  (f_initial : nat -> bool)
  (f_I f_O : nat -> Ty)  
  (T' : Ty)
  (f_proj : [T'] -> forall n, [Option (f_I n)])
  (f_proc : forall n, Proc (f_I n) (f_O n)) : Proc (Times Nat T') (times_on n f_O).
  elim: n.
  - simpl.
    eapply map. simpl.
    instantiate (1:= Times Bool (Option (f_I 0))). exact (fun i => (i.1 == 0, f_proj i.2 0)). 
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
      exact (fun i => (i.1 == n.+1,f_proj i.2 n.+1)).
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

Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.

Definition loop_and_count
  (stateType : Ty)           
  (state : [stateType])
  (T_in T_out T' : Ty)                
  (f_I : [Sum T_in T_out] -> [stateType] -> [stateType])
  (def : [T_out])
  (p : Proc (Times Nat T') T_out)
  (f_si : [Times stateType (Sum T_in T_out)] -> [Option (Times Nat T')])
  : Proc T_in T_out :=
  (@map T_in (Sum T_in T_out) (Sum T_in T_out) T_out inl (inr_or_def def)
                          (@loop (Sum T_in T_out)
                             (@map _ _ (Times _ _) _
                                id snd
                                (@sta _ _ stateType f_I (fun _ v => v) state
                                   (@map (Times stateType (Sum _ _ ))
                                      (Option (Times Nat T')) _ (Sum T_in T_out) f_si inr (maybe p)))))).

(*Definition loop_and_count
  (stateType : Ty)           
  (state : [stateType])
  (T_in' T_out' : Ty)                
  (f_I : [Sum T_in' T_out'] -> [stateType] -> [stateType])
  (def : [T_out'])
  (p : Proc (Times Nat T_in') T_out')
  (f_si : [Times stateType (Sum T_in' T_out')] -> [Option (Times Nat T_in')])
  : Proc T_in' T_out' :=
  (@map T_in' (Sum T_in' T_out') (Sum T_in' T_out') T_out' inl (inr_or_def def)
                          (@loop (Sum T_in' T_out')
                             (@map _ _ (Times _ _) _
                                id snd
                                (@sta _ _ stateType f_I (fun _ v => v) state
                                   (@map (Times stateType (Sum _ _ ))
                                      (Option (Times Nat T_in')) _ (Sum T_in' T_out') f_si inr (maybe p)))))).*)
(*maybe p eliminates input, since we only want it for state change
 very cool, this still wroks for bad example too because we will switch to disk handler after next output
 This is similar to cpu cycle where we check the ic at the end of the cycle.*)

Definition mask := Bool.
Definition pending := Bool.
Definition I_bits := Times pending mask.
Definition ic := Arrow TInterrupt I_bits.
Definition count := Nat.
Definition re_sch := Bool.
Definition prev_pid := Option Nat.
Definition cur_pid := Nat.
Definition pids := Times cur_pid prev_pid.
(*Definition stateType := Times (Times cur_pid re_sch) ic.*)
Definition bool_state := Times re_sch ic.
Definition I_list := List TInterrupt.
Definition stateType := Times pids (Times I_list bool_state).

(*Example*)
Definition my_f_I (n : nat) := fun (n' : nat) => if n' == n.+2 then THandlerOutput else Unit.

Definition I_output_type := Times THandlerOutput bool_state.

Definition my_f_O (n : nat) := fun (n' : nat) => if n' == n.+1 then Nat (*handler*) else if n' == n.+2 then TTypeSyscall else if n' == n.+3 then TPublicOutput else I_output_type.


(*Definition get_count (v : [stateType]) := v.1.1.*)
Definition get_pids (v : [stateType]) := v.1.
Definition get_I_list (v : [stateType]) := v.2.1.
Definition get_bool_state (v : [stateType]) := v.2.2.
Definition get_cur_pid (v : [stateType]) := (get_pids v).1.
Definition get_prev_pid (v : [stateType]) := (get_pids v).2.
Definition get_re_sch (v : [stateType]) := (get_bool_state v).1.
Definition get_ic (v : [stateType]) := (get_bool_state v).2.
Definition get_I_bits' (ic : [ic]) (ir : [TInterrupt]) : [I_bits] := ic ir. 
Definition get_I_bits (v : [stateType]) (ir : [TInterrupt]) := get_I_bits' (get_ic v) ir.

Definition get_pending' (bits : [I_bits]) := bits.1.
Definition get_mask' (bits : [I_bits]) := bits.2.

Definition get_I_pending (v : [stateType]) (ir : [TInterrupt]) := get_pending' (get_I_bits v ir).
Definition get_I_mask (v : [stateType]) (ir : [TInterrupt]) := get_mask' (get_I_bits v ir).

Definition update_pids (v : [stateType]) pids : [stateType] := (pids,v.2).
Definition update_I_list (v : [stateType]) l : [stateType] := (v.1,(l,v.2.2)).
Definition update_bool_state (v : [stateType]) bs : [stateType] := (v.1,(v.2.1,bs)).
Definition update_cur_pid (v : [stateType]) cur_pid : [stateType] := update_pids v (cur_pid,(get_pids v).2).
Definition update_prev_pid (v : [stateType]) prev_pid : [stateType] := update_pids v ((get_pids v).1,prev_pid).
Definition update_re_sch (v : [stateType]) re_sch : [stateType] := update_bool_state v (re_sch,(get_bool_state v).2).
Definition update_I_bits' (myic : [ic])  (ir : [TInterrupt]) (bits : [I_bits]) : [ic] := fun (i : [TInterrupt]) => if i == ir then bits else myic i.

Definition update_ic (v : [stateType]) ic : [stateType] := update_bool_state v ((get_bool_state v).1,ic).
Definition update_I_bits (v : [stateType]) (ir : [TInterrupt]) (bits : [I_bits]) := update_ic v (update_I_bits' (get_ic v) ir bits).

Definition update_I_pending (v : [stateType]) (ir : [TInterrupt]) pending : [stateType] :=
  update_I_bits v ir (pending,get_I_mask v ir).
Definition update_I_mask (v : [stateType]) (ir : [TInterrupt ]) mask : [stateType] :=
  update_I_bits v ir (get_I_pending v ir,mask).

Definition or_I_bits (b1 b2 : [I_bits]) : [I_bits] := (b1.1 || b2.1, b1.2 || b2.2).
Definition or_ic (c1 c2 : [ic]) : [ic] := fun (i : [TInterrupt]) => or_I_bits (c1 i) (c2 i).
Definition or_bool_state (s1 s2 : [bool_state]) : [bool_state] := (s1.1 || s2.1, or_ic s1.2 s2.2).


Definition set_masks (v : [stateType]) : [stateType] := foldr (fun I v' => update_I_mask v' I true) v (get_I_list v).
Definition unset_masks (v : [stateType]) : [stateType] := foldr (fun I v' => if I \in get_I_list v then update_I_mask v' I false else v') v (get_I_list v).
Definition masks_set (v : [stateType]) := foldr (fun I b => (get_I_mask v I) && b) true (get_I_list v).

Definition T_in := Sum TInterrupt Unit.
Definition T_out' (handler_count : nat) := Times (Option TPublicOutput) (Times (Option TTypeSyscall) (Times (Option Nat) (times_on handler_count (fun _ => I_output_type)))).
Definition T' := Option THandlerOutput.
Definition is_sch_out (n : nat) (o : [T_out' n]) :=
  match o with
  | (None,(None,(Some n',_))) => Some n'
  | _ => None                                   
  end.

Definition is_I_in (i : [T_in]) :=
  match i with
  | inl ir => Some ir
  | inr _ => None
  end.

(*Definition all_interrupts : seq [TInterrupt] := [::TimerInterrupt;DiskInterrupt].*)
Definition n_to_I (v : [stateType]) (n : nat) := nth TimerInterrupt (get_I_list v) n.

(* generic version of
match i with
  | (_,(Some (Notify,bstate),_)) => Some (TimerInterrupt,bstate)
  | (Some (Notify,bstate),_) => Some (DiskInterrupt,bstate)
  | _ => None
  end.*)
Definition is_I_out_done (v : [stateType]) (n : nat) (i : [T_out' n]) : [Option (Times TInterrupt bool_state)].
  case: i. move=>_.
  case. move=>_. 
  case. move=>_.
  elim: n. simpl. case. case. move=>_. intros. apply Some. exact (n_to_I v 0,b). exact None.
  simpl. intros.
  case: b. case. case. move=>_. intros. apply Some. exact (n_to_I v n.+1, b).
  intros. apply H in b. apply b.
Defined.    


(*Definition is_I_out_running (i : [T_out']) :=
  match i with
  | (_,(Some (Nothing,_),_)) => Some TimerInterrupt
  | (Some (Nothing,_),_) => Some DiskInterrupt
  | _ => None
  end.*)



Definition is_user_pid (p : [cur_pid]) : bool := (p < 2).
Definition is_handler_pid (p : [cur_pid]) : bool := (2 < p).

(* interrupt handlers live at pids 3 (timer) and 4 (disk) *)
Definition I_handler_pid (v : [stateType]) (ir : [TInterrupt]) : [cur_pid] :=
  3 + index TimerInterrupt (get_I_list v).

(* a handler is selectable iff pending and not masked *)
Definition I_ready (v : [stateType]) (ir : [TInterrupt]) : bool :=
  get_I_pending v ir && ~~ get_I_mask v ir.

(*in prioritised order*) Locate all_interrupts.


Definition first_ready (v : [stateType]) : option [TInterrupt] :=
  ohead [seq ir <-  get_I_list v | (I_ready v ir) ].

(* before overriding cur_pid, save it to prev_pid if it is a user process *)
Definition save_cur_to_prev (v : [stateType]) : [stateType] :=
  if is_user_pid (get_cur_pid v)
  then update_prev_pid v (Some (get_cur_pid v))
  else v.


(*
output scenarios
- a handler finishes
- a handler running, not finished
- scheduler choice
- public/private output

 *)

(*issues*)
Definition f_I (n : nat) (i : [Sum T_in (T_out' n)]) (v : [stateType]) : [stateType] :=
  match i with
  | inl i => if is_I_in i is Some ir then update_I_pending v ir true else v
  | inr o => let v' := if @is_sch_out n o is Some n then update_cur_pid v n else v in (*apply scheduler choice, lowest priority*)
             let v'':= if is_I_out_done v o is Some (ir,bstate) then
                         update_bool_state v' (or_bool_state (get_bool_state (unset_masks v')) bstate) else v in
             match first_ready v'' with
             | Some ir => (update_I_pending (set_masks (update_cur_pid (save_cur_to_prev v) (I_handler_pid v ir))) ir false)
             | None => if is_I_out_done v o is None then v
                       else if (get_re_sch v)
                            then update_re_sch (update_prev_pid (update_cur_pid v 2) None) false
                            else update_prev_pid (update_cur_pid v (odflt 2 (get_prev_pid v))) None
             end
  end.
Print T_out'.

Definition is_I_out (n : nat) (i : [T_out' n]) : [Option THandlerOutput].
  case: i. move=>_.
  case. move=>_. 
  case. move=>_.
  elim: n. simpl. case. case. intros. exact (Some a). exact None.
  simpl. intros.
  case: b. case. case. intros. exact (Some a).
  intros. apply H in b. apply b.
Defined.

Definition f_si (n : nat) (si : [Times stateType (Sum T_in (T_out' n))]) : [Option (Times Nat T')] :=
  if si.2 is inr o then Some (get_cur_pid si.1, @is_I_out n o) else None.

Definition low_p := @out Unit TPublicOutput GetRequest.
Definition high_p := @alternate_generic2 THandlerOutput TTypeSyscall Unit1 Syscall NOP tt (fun i => i == Notify).

Definition handler_type := Proc Unit I_output_type.
Definition false_ic : [ic] := fun _ => (false,false). Print bool_state.
Definition bad_I_handler (re_sch : bool) : handler_type.
  rewrite /handler_type.
  eapply map. exact id.
  instantiate (1:= Times Nat Unit).
  exact (fun o => if o.1 == 0 then (Notify,(re_sch,false_ic)) else (Nothing,(false,false_ic))).
  eapply sta. exact (fun _ v => v). exact (fun _ v => v.+1%%2).
  exact 0.
  apply out. exact tt.
Defined.

Definition bad_tI_handler : handler_type := bad_I_handler true.
Definition bad_dI_handler : handler_type := bad_I_handler false.
Definition default_handler : handler_type := bad_I_handler false.                                                      
  
Definition scheduler : Proc Unit Nat.
  eapply map. exact id.
  instantiate (1:= Times Nat Unit). exact fst.
  eapply sta. exact (fun _ v => v). exact (fun _ v => v.+1%%2).
  exact 0.
  apply out. exact tt.
Defined.

Definition my_procs : forall n, Proc (@my_f_I 1 n) (my_f_O 1 n).
  case. apply bad_tI_handler.
  case. apply bad_dI_handler.
  case. apply scheduler.
  case. apply high_p.  
  case. apply low_p.
  elim. apply default_handler.
  intros. apply default_handler.
Defined.

Definition my_f_coopt (n : nat) : bool := true.
Definition my_f_initial (n : nat) := n == 0. 
Definition f_proj (n : nat) (i : [T']) : forall n', [Option (my_f_I n n')].
  simpl. rewrite /my_f_I. intros. case_if.
  apply i.
  exact (Some tt).
Defined. 
Definition my_process_pool := @process_pool 4 my_f_coopt my_f_initial (my_f_I 1) (my_f_O 1) T' (f_proj 1) my_procs.

Definition initial_state : [stateType] := ((0,None),([::TimerInterrupt;DiskInterrupt],(false,(fun _ => (false,false))))).

Definition def : [ (T_out' 1) ]  := (None,(None,(None,(None,None)))).

Definition model := @loop_and_count stateType initial_state T_in (T_out' 1) T' (@f_I 1) def my_process_pool (@f_si 1).
























  

Definition test := @map (Times Nat (Sum Unit THandlerOutput)) (Times Nat (Times (Option Unit) (Option THandlerOutput))) _ _ (fun i => if snd i is inr ho then (fst i,(None,Some ho)) else (fst i,(Some tt,None))) id
                     (par (@map (Times _ (Times _ _)) (Times _ _) _ _ (fun i => (fst i, (fst (snd i)))) id ((sta_swi true 0 (maybe (low_p)))))
                       (@map (Times _ (Times _ _)) (Times _ _) _ _ (fun i => (fst i, (snd (snd i)))) id ((sta_swi false 1 (maybe (high_p)))))).

Definition intype := Times Nat (Sum Unit THandlerOutput).
Definition intype' := Times Nat (Times (Option Unit) (Option THandlerOutput)).
Definition outtype := Times (Option TPublicOutput) (Option TTypeSyscall).

(*
Say we mapped from unit + handleroutput to intype with handleroutput distinguished
inl tt -> (Some tt,None)
inr hl -> (None, Some ho)

We need (None,Some ho) to be distinguished. Compositionally it means that
Option Unit needs eqmaybe_top _
while Handleroutput suffices with eqmaybe _
Thus (None,None) does not become distinguished, so we don't have to reason about it

schedule is public so publicRel for nat


(*problem in f_EP, we update v to xor v b for any b
 and since state is supposed to be public we cannot opt for the naive solution of making everything distinguished
(what would the problem of that be however? It makes bool rel private as well, which forces us to use oblivious, inconsistent with public output) 
So we need to keep the distinguished set that enters public process empty, so from eqmaybe_top to eqmaybe.
What does that mean for the tuple?
replace eqpair_LR with eqpair_R
it increases set of distinguished pairs, everything is if handleroutput is Some h.

 *)
 *)
Definition test_in_rel : myrel [intype] := eqpair_R (publicRel _) (eqsum_R (publicRel _) (semiprivateRel _)).
Definition test_in_rel' : myrel [intype'] := eqpair_R (publicRel _) (eqpair_R (eqmaybe (publicRel _)) (eqmaybe (semiprivateRel _))).

(*
output rel does not need any tuples distinguished, so eqpair is fine
we also want to keep it public which process was scheduled, so eqmaybe for both types
finally attacker cannot tell difference between secret outputs, so semiprivateRel on right component
 *)
Definition test_out_rel : myrel [outtype] := eqpair (eqmaybe (publicRel _)) (eqmaybe (semiprivateRel _)).
Lemma low_NI : NI test_in_rel test_out_rel test.
Proof. rewrite /test.
       eapply map_NI. instantiate (1:= test_in_rel'). mrw. rewrite /test_in_rel'.
       mrw. intros. apply rel_eqpair_R2' in H. 
       destruct H. 
       destruct H. simpl in H. destruct i,i'. rewrite !pair_rewr in H0. rewrite !pair_rewr. simpl in H. subst.
       have : is_inl i0 /\ is_inl i2 \/ is_inr i0 /\ is_inr i2. de i0. de i2. de i2.
       case. case. intros. destruct i0. destruct i2. done. done. done.
       case. intros. destruct i0. done. destruct i2. done.
       ssa.
       destruct H. destruct i,i'. rewrite !pair_rewr in H,H0.
       destruct i0. done.
       destruct i2. done.
       rewrite !pair_rewr. ssa.  

       mrw. ssa. de i. de s.
       eauto.
       
       simpl in H0.
       apply par_NI.
       eapply map_NI. mrw. intros. rewrite /test_in_rel in H. instantiate (1:= eqpair_R (publicRel _) (eqmaybe (publicRel _))). 
       apply rel_eqpair_R2.
       apply rel_eqpair_R2' in H.
       destruct H. left. destruct H. con. ssa.

       Search _ (rel (eqpair_R _ _)).
       apply rel_eqpair_R2' in H0.
       destruct H0. ssa.
       apply rel_eqpair_R in H0. destruct H0. clear H H1. ssa.
       destruct H. right. ssa.
       mrw. intros. ssa.
       eauto.

       rewrite /sta_swi.
       eapply map_NI. mrw. intros. instantiate (1:= eqpair_R (publicRel _) (eqmaybe_top (publicRel _))).
       destruct i,i'. rewrite !pair_rewr.
       apply rel_eqpair_R2. apply rel_eqpair_R2' in H. destruct H.
       left. ssa. right. ssa.
       mrw. ssa.
       2: eapply sta_NI.
       mrw. intros. apply rel_eqpair in H. destruct H. eauto.
       3: { mrw. intros. simpl in H. destruct i. simpl in H. simpl. destruct i0. simpl in H. done.
            simpl in H.
       
       ssa. de H. rewrite H. de i.de p. de o. de i'. de p. de o. subst. de o0. de o1. de H1. de o1. ssa.
  rewrite /sta_low_p /sta_swi.
  eapply map_NI.
  mrw. intros. instantiate (1:= (eqpair (publicRel _) (publicRel _))). simpl. ssa.
  mrw. ssa.
  mrw. intros.
  2: eapply sta_NI. Search _ (rel (eqpair _ _)). apply rel_eqpair in H. destruct H. eauto.
  4: { eapply map_NI. mrw. intros. 





      
Definition low_in_rel := public




Definition handler := @alternate_generic TInterrupt THandlerOutput Unit2 Notify Nothing tt.
Definition unit_p : Proc Unit Unit := @out Unit Unit tt.

Definition my_procs : forall n, Proc (my_f_I n) (my_f_O n).
  case. apply handler.
  case. apply high_p.
  case. apply low_p.
  elim. apply unit_p.
  intros. apply unit_p.
Defined.

Definition my_f_coopt (n : nat) : bool := n == 0.
Definition my_f_initial (n : nat) := n == 0.
Definition my_process_pool := @process_pool 2 my_f_coopt my_f_initial my_f_I my_f_O my_procs.

Definition my_T_in := Sum Unit TInterrupt. (*We need Unit input to be able to differentiate trace, otherwise we only have interrupts in the trace*)
Definition my_T_out := Option (Sum TPublicOutput TTypeSyscall).
Definition my_T_in' := times_Option_n 2 my_f_I.
Definition my_T_out' := times_Option_n 2 my_f_O.

Definition h_pub := (false,false).
Definition h_pr := (false,true).
Definition pub := (true,false).
Definition pr := (true,true).

Definition good_schedule (i : [Sum my_T_in my_T_out']) (v : [bstate]) : [bstate] :=
  let: (proc_state,flag) := v in
  if proc_state == pub then match i with | inl (inr TimerInterrupt) => (h_pub,false) | inl (inr DiskInterrupt) => (pub,true) | _ => (pub,true) end
  else if proc_state == h_pub then match i with | inr _ => (pr,false) | inl (inr DiskInterrupt) => (h_pub,true) | _ => (h_pub,false) end
  else if proc_state == pr then match i with inl (inr TimerInterrupt) => (h_pr,false) | inl (inr DiskInterrupt) => (pr,true) | _ => (pr,true) end
  else if proc_state == h_pr then match i with | inr _ => (pub,false) | inl (inr DiskInterrupt) => (h_pr,true)  | _ => (h_pr,false) end
  else v.

(*Definition good_schedule (i : [Sum my_T_in my_T_out']) (v : [nbstate]) : [nbstate] :=
  match fst v,i with
  | (true,false),(inl (inr TimerInterrupt)) => (h_pub,(0,2))                                                 
  | (true,false),_  => (pub,(3,4))
  | (false,false), inr _ => (pr,(1,1))
  | (false,false), _ => (pr,(3,5))
  | (true,true), (inl (inr TimterInterrupt)) => (h_pr,(0,1))
  | (true,true), _ => (pr,(3,6))
  | (false,true), inr _ => (pub,(2,2))
  | bb,_ => (bb,(3,3))
end. *)              

Definition bad_schedule (i : [Sum my_T_in my_T_out']) (v : [nbstate]) : [nbstate] :=
  match fst v,i with
  | (false,false), inr _ => (pr,(1,1))
  | (false,false), inl _ => (h_pub,(3,3))                            
  | (false,true), inr _ => (pr,(1,1))
  | (false,true), inl _ => (h_pr,(3,3))
  | (true,false), inr _ => (pub,(3,3))
  | (true,false), inl (inr DiskInterrupt) => (h_pub,(0,2))
  | (true,false), inl (inr TimerInterrupt) => (pr,(1,2))                                      
  | (true,true), inr _ => (pr,(3,3))
  | (true,true), inl (inr DiskInterrupt) => (h_pr,(0,1))
  | (true,true), inl (inr TimerInterrupt) => (pub,(2,1))
  | bb,_ => (bb,(3,3))                                             
  end.

Definition none3 : [ (times_Option_n 2 my_f_I) ]  := (None,(None,None)).


Definition my_f_route (t : [my_T_out']) : [my_T_in'] :=
  match t with
  | ((Some publ, _)) => none3
  | (None,(Some prv,_)) => none3
  | (None,(None,Some handl)) => (None,(Some handl,None))
  | _ => none3 
  end.

Definition my_f_in (t : [my_T_in]) : [ (times_Option_n 2 my_f_I) ] :=
  match t with
  | inl tt => (Some tt,(None,None))
  | inr TimerInterrupt => none3
  | inr DiskInterrupt => (None,(None,Some DiskInterrupt)) end.

Definition my_f_out (t : [my_T_out']) :=
  match t with
  | (Some publ, (None, None)) => Some (inl publ)
  | (None, (Some pr, None)) => Some (inr pr)
  | _ => None (*includes handler output and simultaneous output*)
  end.

Definition f_out_helper (t : [my_T_out]) (h : [THandlerOutput]) : [my_T_out'] :=
  match t with
  | Some (inl publ) => (Some publ, (None,None))
  | Some (inr pr) => (None, (Some pr, None))
  | None => (None,(None,Some h))
  end.            
Check loop_and_count.
Definition to_nats (s : [bstate]) :=
  let: (proc_state,flag) := s in
  if flag then (3,3) else
    match proc_state with
    | (true,false) => (2,2)
    | (false,false) => (0,2)
    | (true,true) => (1,1)
    | (false,true) => (0,1)                                            
    end.

Definition model' := @loop_and_count bstate (h_pr,false) to_nats my_T_in my_T_in' my_T_out' my_T_out' good_schedule my_f_route def my_process_pool my_f_in.
Definition model := @map _ _ _ (Option (Sum TPublicOutput TTypeSyscall)) id my_f_out model'.
Definition bad_model' := @loop_and_count nbstate (h_pr,(3,3)) snd my_T_in my_T_in' my_T_out' my_T_out' bad_schedule my_f_route def my_process_pool my_f_in.
Definition bad_model := @map _ _ _ (Option (Sum TPublicOutput TTypeSyscall)) id my_f_out bad_model'.
Definition out0 x : [my_T_out'] := (Some x,(None,(None))).
Definition out1 x : [my_T_out'] := (None,(Some x,(None))).
Definition out2 x : [my_T_out'] := (None,(None,(Some x))).

(*Spec for good scheduler*)
Definition Tsum' := ([my_T_in] + [my_T_out'])%type.
Definition Tsum := ([my_T_in] + [my_T_out])%type.
Definition seqtype' := seq Tsum'.
Definition seqtype := seq Tsum.
Definition tI' : Tsum'  := inl (inr TimerInterrupt).
Definition dI' : Tsum'  := inl (inr DiskInterrupt).
Definition tI : Tsum  := inl (inr TimerInterrupt).
Definition dI : Tsum  := inl (inr DiskInterrupt).
Definition pub_get' : Tsum' := inr (Some GetRequest,(None,None)).
Definition pub_get : Tsum := inr (Some (inl GetRequest)).
Definition pub_nop' : Tsum' := inr (Some Public_NOP,(None,None)).
Definition pub_nop : Tsum := inr (Some (inl (Public_NOP))).
Definition pr_sys' : Tsum' := inr (None,(Some Syscall,None)).
Definition pr_sys : Tsum := inr (Some (inr Syscall)).
Definition pr_nop' : Tsum' := inr (None,(Some NOP,None)).
Definition pr_nop : Tsum := inr (Some (inr NOP)).
Definition handl_out_noti' : Tsum' := inr (None,(None,Some Notify)).
Definition handl_out_noth' : Tsum' := inr (None,(None,Some Nothing)).
Definition handl_out : Tsum := inr None.
Definition non' : Tsum' := inr (None,(None,None)).
Definition non : Tsum := inr None.

Definition no_dI' : seqtype' :=   [::handl_out_noth';pub_get';    pub_get';tI';handl_out_noth';pr_nop'(*nop*);pr_nop';tI';handl_out_noth';pub_get'].
Definition with_dI' : seqtype' := [::handl_out_noth';pub_get';dI';pub_get';tI';handl_out_noti';pr_sys'(*sys*);pr_nop';tI';handl_out_noth';pub_get'].
Definition no_dI : seqtype :=   [::handl_out;pub_get;    pub_get;tI;handl_out;pr_nop(*nop*);pr_nop;tI;handl_out;pub_get].
Definition with_dI : seqtype := [::handl_out;pub_get;dI;pub_get;tI;handl_out;pr_sys(*sys*);pr_nop;tI;handl_out;pub_get].

Definition output_rel' := eqpair (eqmaybe (publicRel TPublicOutput)) (eqpair (eqmaybe (semiprivateRel TTypeSyscall)) (eqmaybe (semiprivateRel THandlerOutput))).
Definition output_rel := eqmaybe (eqsum_R (publicRel TPublicOutput) (semiprivateRel TTypeSyscall)).

Ltac rewr := rewrite /model /model' /loop_and_count /my_process_pool /process_pool /my_f_initial /low_p /my_f_coopt /handler /alternate_generic /alternate_generic2 /high_p.
Lemma trace_no_dI' : forall l, Trace output_rel' l no_dI' model'.
  intros.
  rewr. simpl. rewr. simpl. rewr.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. rewrite !inE. cbn.
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
Qed.

Lemma trace_with_dI' : forall l, Trace output_rel' l with_dI' model'.
  rewr. simpl. rewr. simpl. rewr.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. rewrite !inE. cbn.
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
Qed.

(*Necessary to avoid controlled_eauto tactic weirdness in reduce_tac*)
Ltac reduce_tac2 :=
  (try rewr);
   (repeat
      reduce_once);(try swi_instans); rewrite ?eqxx /= /xor /=.


Lemma trace_no_dI : forall l, Trace output_rel l no_dI model.
  rewr. simpl. rewr. simpl. rewr.
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out2 Nothing)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 
  
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ. reduce_tac2;reduce_tac2;try econ.

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out2 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.  

  econ. reduce_tac2;reduce_tac2;try econ.
  
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out2 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.
  done.
Qed.

Lemma trace_with_dI : forall l, Trace output_rel l with_dI model.
  rewr. simpl. rewr. simpl. rewr.
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out2 Nothing)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 
  
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.

  econ. reduce_tac2;reduce_tac2;try econ. reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:=  (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ. reduce_tac2;reduce_tac2;try econ.

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out2 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.  

  econ. reduce_tac2;reduce_tac2;try econ.
  
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out2 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.
  done.
Qed.


Definition bad_no_dI' : seqtype' :=   [::handl_out_noth';tI';pub_get';                                        pub_get';tI';pr_nop';pr_nop';tI';pub_get'].
Definition bad_with_dI' : seqtype' := [::handl_out_noth';tI';pub_get';dI';handl_out_noti';pr_sys';pr_nop';tI';pub_get';tI';pr_nop';pr_nop';tI';pub_get'].

Definition bad_no_dI : seqtype :=     [::handl_out;      tI; pub_get;                                         pub_get;tI;pr_nop;pr_nop;tI;pub_get].
Definition bad_with_dI : seqtype :=   [::handl_out;tI;pub_get;dI;handl_out;pr_sys;pr_nop;tI;pub_get;tI;pr_nop;pr_nop;tI;pub_get].

Ltac rewr ::= rewrite /model /model' /bad_model /bad_model' /loop_and_count /my_process_pool /process_pool /my_f_initial /low_p /my_f_coopt /handler /alternate_generic /alternate_generic2 /high_p.

Lemma bad_trace_no_dI' : forall l, Trace output_rel' l bad_no_dI' bad_model'.
  intros.
  rewr. simpl. rewr. simpl. rewr.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].  
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. cbn.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. 
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].  
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].    
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. 
Qed.

Lemma bad_trace_with_dI' : forall l, Trace output_rel' l bad_with_dI' bad_model'.
  intros.
  rewr. simpl. rewr. simpl. rewr.
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].  
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].    
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac]. 
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].    
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; first reduce_tac;try solve [ reduce_tac;reduce_tac].
  econ; [ idtac | apply rel_refl | idtac ];first reduce_tac;try solve [ reduce_tac;reduce_tac].  
Qed.

Lemma bad_trace_no_dI : forall l, Trace output_rel l bad_no_dI bad_model.
Proof.
  rewr. simpl. rewr. simpl. rewr.
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out2 Nothing)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ. reduce_tac2;reduce_tac2;try econ.
  
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ. reduce_tac2;reduce_tac2;try econ.

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.  

  econ. reduce_tac2;reduce_tac2;try econ.
  
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.
  done.
Qed.

Lemma bad_trace_with_dI : forall l, Trace output_rel l bad_with_dI bad_model.
Proof.
  rewr. simpl. rewr. simpl. rewr.
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out2 Nothing)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ. reduce_tac2;reduce_tac2;try econ.
  
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.

  econ. reduce_tac2;reduce_tac2;try econ. reduce_tac.

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out2 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.  

  econ. reduce_tac2;reduce_tac2;try econ.
  
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.

  econ. reduce_tac2;reduce_tac2;try econ.

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac. 

  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out1 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.  

  econ. reduce_tac2;reduce_tac2;try econ.
  
  econ;[ idtac | apply rel_refl | idtac ]. reduce_once. instantiate (1:= (out0 _)). done.
  reduce_tac2;reduce_tac2;try econ;try econ;reduce_tac.  
  
  done.
Qed.




(*Lemma NI_model : NI input_rel' output_rel model.  
Admitted.*)


(*Definition is_tI_in (i : [T_in']) :=
  match i with
  | (_,(Some _,_)) => true
  | _ => false                              
  end.

Definition is_dI_in (i : [T_in']) :=
  match i with
  | (Some _,_) => true
  | _ => false                              
  end.*)


(*Definition is_tI_out_done (o : [T_out']) :=
  match o with
  | (_,(Some Notify,_)) => true
  | _ => false   
  end.

Definition is_tI_out_running (o : [T_out']) :=
  match o with
  | (_,(Some Nothing,_)) => true
  | _ => false   
  end.

Definition is_dI_out_done (o : [T_out']) :=
  match o with
  | (Some Notify,_) => true
  | _ => false 
  end.

Definition is_dI_out_running (o : [T_out']) :=
  match o with
  | (Some Nothing,_) => true
  | _ => false 
  end.*)

(*Definition incoming_tI (v : [stateType]) : [stateType] :=
  let tI_bits := if negb (get_tI_mask v) then (false,true) else (true,true) in
  update_tI_bits v tI_bits.


Definition incoming_dI (v : [stateType]) :=
  let bb := v.2.2 in
  let bb' := if negb bb.2 then (false,true) else (true,true) in
  (v.1,(v.2.1,bb')).

Definition outgoing_tI (v : [stateType]) :=
  let bb := v.2.1 in
  let bb' := if bb.1 then (false,true) else (false,false) in
  (v.1,(bb',v.2.2)).

Definition outgoing_dI (v : [stateType]) :=
  let bb := v.2.2 in
  let bb' := if bb.1 then (false,true) else (false,false) in
  (v.1,(v.2.1,bb')).*)
