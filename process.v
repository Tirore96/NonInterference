
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

Fixpoint times_N n (f : nat -> Ty) : Ty :=
  let t := f n in
  match n with
  | 0 => t
  | S n' => Times t (times_N n' f)
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
                                      | _ => Unit
                                      end.

Definition my_f_O := fun (n : nat) => match n with
                                      | 0 => THandlerOutput
                                      | 1 => TTypeSyscall
                                      | 2 => TPublicOutput
                                      | _ => Unit
                                      end.



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

Definition process_pool
  (n : nat)
  (f_coopt : nat -> bool)
  (f_initial : nat -> bool)
  (f_I f_O : nat -> Ty)
  (f_proc : forall n, Proc (f_I n) (f_O n)) : Proc (Times (Times Nat Nat) ((times_Option_n n f_I))) (times_Option_n n f_O).
  elim: n.
  - simpl.
    eapply map. simpl.
      instantiate (1:= Times Bool (Option (f_I 0))). exact (fun n => ((0 \in [:: fst (fst n); snd (fst n)],snd n))).
      exact id. 
    eapply swi. exact (f_initial 0). 
    eapply maybe. 
    eapply map.
      eapply id. 
      exact (fun o => (f_coopt 0,o)).
    exact (f_proc 0).

  - intros. simpl.
    eapply par.
    * eapply map.
      instantiate (1:= Times Bool (Option (f_I n.+1))). simpl.
      exact (fun x => ((n.+1) \in [:: fst (fst x); snd (fst x)], fst (snd x))).
        exact id. 
      eapply swi.
        exact (f_initial n.+1). 
      eapply maybe.
      eapply map.
        exact id.     
        exact (fun o => (f_coopt n.+1,o)).
      (*eapply maybe.*) (*not necessary anymore*)
      exact (f_proc n.+1).
    * eapply map. 3: apply H. simpl. 
      exact (map_pair id snd).
      exact id. 
Defined.

Definition inr_or_def {A B : Set} (def: B) (x : A + B) := if x is inr x' then x' else def.

Definition nbstate := Times (Times Bool Bool) (Times Nat Nat). (*((b1,b2),(turn_on,turn_off)*)
(*b1,b2 = state
  FF = handler from public
  FT = handler from private
  TF = public
  TT ) private
 *)
      
Definition loop_and_count
  (state : [nbstate])           
  (T_in T_in' T_out T_out' : Ty)                
  (f_I : [Sum T_in T_out'] -> [nbstate] -> [nbstate])
  (f_route : [T_out'] -> [T_in'])
  (def : [T_out'])
  (p : Proc (Times (Times Nat Nat) T_in') T_out')
  (f_in : [T_in] -> [T_in'])
  : Proc T_in T_out' :=
  (@map T_in (Sum T_in T_out') (Sum T_in T_out') T_out' inl (inr_or_def def)
                          (@loop (Sum T_in T_out')
                             (@map _ _ (Times _ _) _
                                id snd
                                (@sta _ _ nbstate f_I (fun _ v => v) state
                                   (@map (Times nbstate (Sum _ _ ))
                                      (Times (Times Nat Nat) T_in')
                                _ (Sum _ _)
                                (fun i  =>
                                   match snd i with
                                   | inl i' => (snd (fst i),f_in i')
                                   | inr o  => (snd (fst i),f_route o) (*i tilfælde hvor vi både ændrer switch og rerouter input, problem?*)
                                   end) inr
                                p))))).


Definition low_p := @out Unit TPublicOutput GetRequest.
Definition handler := @alternate_generic TInterrupt THandlerOutput Unit2 Notify Nothing tt.
Definition high_p := @alternate_generic2 THandlerOutput TTypeSyscall Unit1 Syscall NOP tt (fun i => i == Notify).
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

Definition good_schedule (i : [Sum my_T_in my_T_out']) (v : [nbstate]) : [nbstate] :=
  match fst v,i with
  | (true,false),(inl (inr TimerInterrupt)) => (h_pub,(0,2))                                                 
  | (true,false),_  => (pub,(3,4))
  | (false,false), inr _ => (pr,(1,1))
  | (false,false), _ => (pr,(3,5))
  | (true,true), (inl (inr TimterInterrupt)) => (h_pr,(0,1))
  | (true,true), _ => (pr,(3,6))
  | (false,true), inr _ => (pub,(2,2))
  | bb,_ => (bb,(3,3))
end.               

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
Definition def : [ (times_Option_n 2 my_f_O) ]  := (None,(None,None)).

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
                                                                   
Definition model' := @loop_and_count (h_pr,(3,3)) my_T_in my_T_in' my_T_out' my_T_out' good_schedule my_f_route def my_process_pool my_f_in.
Definition model := @map _ _ _ (Option (Sum TPublicOutput TTypeSyscall)) id my_f_out model'.
Definition bad_model' := @loop_and_count (h_pr,(3,3)) my_T_in my_T_in' my_T_out' my_T_out' bad_schedule my_f_route def my_process_pool my_f_in.
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
