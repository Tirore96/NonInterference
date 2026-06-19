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
                                      | 3 => Sum TInterrupt THandlerOutput (*scheduler*)
                                      | _ => Unit
                                      end.

Definition my_f_O := fun (n : nat) => match n with
                                      | 0 => THandlerOutput
                                      | 1 => TTypeSyscall
                                      | 2 => TPublicOutput
                                      | 3 => Times Nat Nat
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
Definition good_schedulerp :  Proc (Sum TInterrupt THandlerOutput) (Times Nat Nat). (*handlerflag, processflag*) Check sta_NI. Check swi_NI. 
  eapply map. apply id. instantiate (1:= Times (Times Bool Bool) Unit).
  exact (fun o => match fst o with | (true,false) => (3,1) | (true,true) => (2,1) | (false,true) => (3,3) | (false,false) => (2,2) end ).
  eapply (@sta _ _ _). exact (fun ih bb => match ih with | inl TimerInterrupt => (true,~~ (snd bb))
                                                         | inr _ => (false,snd bb)
                                                         | _ => bb          
                                           end).
  exact (fun _ bb => bb).
  exact (false,false).
  eapply out. con.
Defined.

Definition sstream := Stream ([(Sum TInterrupt THandlerOutput)] + [(Times Nat Nat)]).

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
Qed.

Lemma schedulerp_trace : trace my_sstream good_schedulerp.
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
Qed.


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
  | (Some sch,_) => (sch,none4)
  | (_ ,(Some publ, _)) => ((0,0),none4)
  | (_ ,(None,(Some prv,_))) => ((0,0),none4)
  | (_ ,(None,(None,Some handl))) => ((1,4),(Some (inr handl),(None,(Some handl,None)))) (*(1,4) = turn off yourself, turn on scheduler*)
  | _ => ((0,0),none4)    
  end.

Definition my_f_in_sch_good (t : [my_T_in]) : [Times Nat Nat] := match t with | inl tt | inr DiskInterrupt => (0,0) | inr TimerInterrupt => (0,4) end.
Definition my_f_in_t (t : [my_T_in]) : [ (times_Option_n 3 my_f_I) ] := match t with
                                                                        | inl tt => (None,(Some tt,(None,None)))
                                                                        | inr TimerInterrupt => (Some (inl TimerInterrupt),(None,(None,None)))
                                                                        | inr DiskInterrupt => (None,(None,(None,Some DiskInterrupt))) end.
Definition my_f_in_good (t : [my_T_in]) : [my_T_in'] := (my_f_in_sch_good t, my_f_in_t t).
Definition my_f_out (t : [my_T_out']) := match t with
                                         | (_,(Some p,(None,None))) => Some (inl p)
                                         | (_,(None,(Some sys,None))) => Some (inr sys)
                                         | _ => None
                                         end.

Definition f_out_dis (v : [my_T_out]) := match v with | Some (inl _) | None => False | _  => True end.

Definition my_f_out_rel : myrel ([my_T_out]).
  refine (@MyRel _
            (fun l (v : [my_T_out]) => l = \bot /\ f_out_dis v )
            (fun l v1 v2 => v1 = v2 \/ (l = \bot /\ f_out_dis v1 /\ f_out_dis v2))
            _
            _
            _
            _).
  intros. con. intro. auto. intro. intros. de H.
  intro. intros. de H. de H0. left. subst. auto. subst. eauto.
  de H0. subst. eauto.
  intros. de H0.
  intros. ssa. subst. apply order_bot in H. subst. ssa.
  intros. ssa. subst. rewrite /order in H.  rewrite lex0 in H. by apply/eqP.
  ssa.
  con. case. intros. eauto.
  case. intros. subst. eauto.
  ssa.
Defined.

Definition my_only_loop_good' := @only_loop my_T_in' my_T_out' my_f_route_good my_def process_pool_good.

Definition my_only_loop_good : Proc my_T_in my_T_out .
  eapply map. apply my_f_in_good. apply my_f_out. apply my_only_loop_good'.
Defined.

  

Definition out0 x : [my_T_out'] := (Some x,(None,(None,None))).
Definition out1 x : [my_T_out'] := (None,(Some x,(None,None))).
Definition out2 x : [my_T_out'] := (None,(None,(Some x,None))).
Definition out3 x : [my_T_out'] := (None,(None,(None, Some x))).

(*Spec for good scheduler*)
(*Add diskinterrupt*)
Definition streamType' := Stream ([my_T_in'] + [my_T_out']).
Definition newtrace'F (s : streamType') := Cons (inl (my_f_in_good (inr TimerInterrupt))) (*jump to scheduler*)
                                             (Cons (inr ((Some (2,1)),(None,(Some NOP,None)))) (*private process does nothing, scheduler points to handler*)
                                             (Cons (inr (out3 Nothing)) (*handler finishes, returns control to scheduler*)
                                             (Cons (inr (out0 (3,3))) (*scheduler points to public*)
                                             (Cons (inr (out1 GetRequest)) (*public output*)
                                             (Cons (inl (my_f_in_good (inr DiskInterrupt)))(*disk interrupt, should NOT jump to handler*)
                                             (Cons (inl (my_f_in_good (inr TimerInterrupt))) (*jump to scheduler*)
                                             (Cons (inr (Some (3,1),(Some GetRequest,(None,None)))) (*public process finishes, scheduler points to handler*)
                                             (Cons (inr (out3 Notify)) (*handler signal informs diskinterrupt was received*)
                                             (Cons (inr (out0 (2,2))) (*scheduler points to private*)
                                             (Cons (inr (None,(None,(Some Syscall,None)))) s)))))))))) (*private output received notification from handler, outputs new syscall*).

CoFixpoint newtrace' := newtrace'F newtrace'.

Lemma newtrace'_eq : newtrace' = newtrace'F newtrace'.
Proof.
rewrite {1}/newtrace'.
rewrite {1}(coseq_match (cofix newtrace' : streamType' := newtrace'F newtrace')).
simpl.
rewrite /newtrace'F.
do ? f_equal.
Qed.



Definition streamType := Stream ([my_T_in] + [my_T_out]).

Definition newtraceF (s : streamType) := Cons (inl (inr TimerInterrupt))
                                            (Cons (inr (Some (inr NOP)))
                                             (Cons (inr None)
                                             (Cons (inr None)
                                             (Cons (inr (Some (inl GetRequest)))
                                             (Cons (inl (inr DiskInterrupt))
                                             (Cons (inl (inr TimerInterrupt))
                                             (Cons (inr (Some (inl GetRequest)))
                                             (Cons (inr None)
                                             (Cons (inr None)
                                             (Cons (inr (Some (inr Syscall))) s)))))))))).

CoFixpoint newtrace := newtraceF newtrace.

Lemma newtrace_eq : newtrace = newtraceF newtrace.
Proof.
rewrite {1}/newtrace.
rewrite {1}(coseq_match (cofix newtrace : streamType := newtraceF newtrace)).
simpl.
rewrite /newtraceF.
do ? f_equal.
Qed.


Ltac rewr ::=  (try rewrite newtrace'_eq); (try rewrite newtrace_eq); rewrite /low_p /handler /high_p /only_loop /my_only_loop_good' /my_only_loop_good /process_pool_good /good_schedulerp /my_f_coopt /scheduled_process_pool /high_p /alternate_generic /alternate_generic2 /low_p.

(*spec for good scheduler*)
Lemma newtrace'_trace : trace newtrace' my_only_loop_good'.
Proof.
  pcofix CIH. 
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  instantiate (1:= 0). instantiate (1:= 0). instantiate (1:= 0). simpl.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;right.
  swi_instans. simpl. eauto.
Qed.


(*spec for good scheduler (what the world sees)*)
Lemma newtrace_trace : trace newtrace my_only_loop_good.
Proof.
  pcofix CIH.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.
  bundle;left.  
  bundle;left.
  bundle.
  instantiate (2:= None). simpl.
  instantiate (1:= None). simpl. done.
  instantiate (3:=0). simpl. reduce_once. econ.
  reduce_tac.
  instantiate (2:= 0). simpl.
  reduce_once.
  instantiate (2:= 0). simpl.
  reduce_once.
  simpl. reduce_once. econ.
  reduce_tac.
  reduce_tac.
  reduce_tac.
  reduce_tac.
  left.
  
  bundle;left.
  bundle;left.  
  bundle;right.
  swi_instans.
  eauto.
Qed.





(*Now the bad process*)


(*
private on ->(?tI)
private on, scheduler on ->(!public)
public on ->(?dI)
public on, handler on -> !(public,notification)
public on ->(?tI)
scheduler on, public on ->(!handler)
handler on ->(!notification)
scheduler on ->(!private)
...
 *)
Definition good_schedulerp :  Proc (Sum TInterrupt THandlerOutput) (Times Nat Nat). (*handlerflag, processflag*)
  eapply map. apply id. instantiate (1:= Times (Times Bool Bool) Unit).
  exact (fun o => match fst o with | (true,false) => (3,1) | (true,true) => (2,1) | (false,true) => (3,3) | (false,false) => (2,2) end ).
  eapply (@sta _ _ _). exact (fun ih bb => match ih with | inl TimerInterrupt => (true,~~ (snd bb))
                                                         | inr _ => (false,snd bb)
                                                         | _ => bb          
                                           end).
  exact (fun _ bb => bb).
  exact (false,false).
  eapply out. con.
Defined.
