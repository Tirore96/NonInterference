See hash: 4bc91b23fea59b21cdb31aa868a0ec3427cbabf3
for version that compiles these examples.            

Module Example1.
(*Process*)
Definition p_high := @out TInput TOutput Step.
Definition p_low := @out TInput TOutput Idle.
Definition process_pool := par_swiI false p_high p_low. (*both p_high and p_low receive inputs no matter who was scheduled. This is because par_swiI does not filter input. p_high and p_low don't change state based on input so it is fine in this example*)

Definition scheduler (p : Proc (Times Bool (Times TInput TInput)) (Times (Option TOutput) (Option TOutput))) :=
  @map _ (Times Bool (Times TInput TInput)) _ _ (fun (i : [TInput]) => (i == DiskRead,(i,i))) id p.

(*Trace*)
Definition newtraceF_simple (newtrace : streamType) := Cons (inr (None, Some Idle))
                                                         (Cons (inl (DiskRead))
                                                           (Cons (inr (Some Step,None))
                                                                  (Cons (inl (DiskRead)) newtrace))).
CoFixpoint newtrace_simple := newtraceF_simple newtrace_simple.

Lemma newtrace_simple_eq : newtrace_simple = newtraceF_simple newtrace_simple.
Proof.
rewrite {1}/newtrace_simple.
rewrite {1}(coseq_match (cofix newtrace : streamType := newtraceF_simple newtrace)).
simpl.
rewrite /newtraceF_simple.
do ? f_equal.
Qed.


(*Trace derivation*)
Ltac rewr ::=  (try rewrite newtrace_simple_eq); rewrite /newtraceF_simple /process_pool /par_swiI /scheduler /p_high /p_low.
Check process_pool.
Lemma simple_trace : trace newtrace_simple (scheduler process_pool).
Proof.
  pcofix CIH.
  rewr.
  bundle. left.
  bundle. left.
  bundle. left.
  bundle. right.
  swi_instans. eauto.
Qed.

Definition InputRel : myrel ([TInput]). 
  refine (@MyRel _
            (fun l a => l = \bot /\ a = DiskRead)
            (fun l a b => a = b) _ _ _ _).
  intros.
  done.
  intros. ssa. subst. subst. subst.
  Search _ order.
  move/order_bot : H. move=>->. done.
  intros. ssa. subst. con.
  ssa.
  ssa.
Defined.  

(*NotSim*)
Example counterexample : NotSim \bot InputRel (publicRel _) newtrace_simple (scheduler process_pool).
Proof. 
  rewrite newtrace_simple_eq /newtraceF_simple.
  apply:NS4. ssa. de o'. subst.
  
  apply: NS2. instantiate (1:= (DiskRead)).
  ssa.

  intros. match_dd.

  apply: NS3. ssa. de x. subst.
  match_dd.
  
  apply: NS4. ssa. de o'. subst.
  match_dd.
Qed.

(*Not NI*)
Example example_not_NI :  ~ NI InputRel (publicRel _) (scheduler process_pool).
Proof.
  rewrite /NI. ssa. intro.

  apply/toNotSim. apply/counterexample.
  apply/H. apply simple_trace.
Qed.
End Example1.
