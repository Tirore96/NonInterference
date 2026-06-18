  
  (*consider using the simplified scheduled process_pool once proof has been fixed*)
  (*TODO: wrap this in output rel with only one None*)
Lemma main_NI : @NI _ _ (eqsum_R (publicRel _ ) (semiprivateRel _))
                  my_f_out_rel
                  (@map _ _ _ (Option (Option (Sum TPublicOutput TTypeSyscall))) my_f_in my_f_out
                     (my_loop_and_count
                        (@scheduled_process_pool 2 my_f_I my_f_O (@my_f_sch my_f_I) my_procs))).
Proof.
  eapply map_NI. 
  instantiate (1:= @eqpair_REQ (Option _) _ None (eqpair_LR (eqmaybe_top (semiprivateRel THandlerOutput)) (eqmaybe_top (semiprivateRel TInterrupt)))).

  mrw. intros.
  have: is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'. de i. de i'. de i'.
  case;split_and. de i. de i'. subst. de u.
  de i. de i'.
  mrw. intros.
  destruct i. rewrite /my_f_in. destruct i. ssa. simpl. simpl in H.
  ssa. 

  mrw. intros. move: H. instantiate (1:= intermediate_outputRel ). (*replaced eqpair_OR with eqpair_LR because we need enough information about distinguishability so that we don't do None vs Some case distinction in i1 and i2 when relating (x,i1,y) and (x',i2,y) *)
  (*we needed eqpair_OR because we used eqmaybe in secret processes*)
  (*we did that to get (none,none,none) as public*)
  (*more generally we did it to minimise what is distinguished*)
  (*eqpair_LR makes (none,none,none) private*)
  (*what does this mean for the output type the word sees?*)
  intros. 
  destruct i,i'. destruct i0,i2.
  apply rel_eqpair in H. destruct H.
  apply rel_eqpair in H0. destruct H0.
  rewrite !pair_rewr in H,H0,H1.
  apply rel_eqmaybe_swi2 in H,H0,H1.
  destruct H. split_and;subst.
  destruct H0. split_and;subst.
  destruct H1. split_and;subst. split_and;subst.
  destruct H. split_and;subst.
  destruct H1. split_and;subst. ssa.
  destruct H. split_and;subst. ssa. subst. ssa.
  split_and;subst. 
  de i3. de i4.
  split_and. de i0. de i2.
  destruct H. split_and.
  destruct H0. split_and.
  destruct H1. split_and. ssa.
  destruct H. split_and. ssa. de H2. subst. auto.
  split_and. de i3. de i4.
  destruct H. split_and.
  destruct H1. split_and. ssa.
  destruct H. split_and. ssa.
  split_and. de i3. subst. de i4.
  split_and. de i0. de i2.
  destruct H1. split_and. de H3. subst. destruct H1. split_and. ssa.
  split_and. de i3. de i4.
  split_and. de i.
  
  apply/map_NI.
  4: apply/loop_NI.
  mrw. intros. apply rel_eqsum_L. (*R = output, not distinguished*) eapply H.
  mrw. intros. apply dis_eqsum_L. done.

  instantiate (1:= intermediate_outputRel). 

  mrw. intros.
  have: is_inl i /\ is_inl i' \/ is_inr i /\ is_inr i'. de i. de i'. de i'.
  case;split_and. de i. de i'. de i'. de i'.
  de i. de i'. de i'. de i'.

  eapply map_NI.
  4: apply sta_NI.
  apply f_NI_id.
  apply f_PU_id. 
  
  mrw. intros. apply rel_eqpair in H. destruct H. eauto.


  (*Trying to work on side conditions here, should not affect the rest of the proof because of 4: {*)
  2: { mrw. intros. eapply H0. } 
  shelve.
  mrw. intros. eauto.

(*  instantiate (1:=  publicRel _).*)
(*  mrw;ssa.
  mrw;ssa.
  mrw;ssa.*)

  eapply map_NI.
  
  instantiate (1:= @eqpair_REQ Nat _ 0 (@eqpair_REQ (Option _) _ None (eqpair_LR (eqmaybe_top (semiprivateRel THandlerOutput)) (eqmaybe_top (semiprivateRel TInterrupt))))). (*eqmaybe is correct?*)
  mrw. intros.
  destruct i. destruct i'. rewrite !pair_rewr.
  have: is_inl i0 /\ is_inl i2 \/ is_inr i0 /\ is_inr i2. ssa. de H. subst. de i0. de i2. de i2. de i0. de i2.
  case;split_and. destruct i0. destruct i2.
  ssa. destruct H. ssa. ssa.
  right. ssa. ssa. ssa. destruct i0. ssa. destruct i2. ssa. ssa.
  destruct H. ssa. left. ssa.
  move: H. instantiate (1:= publicRel _). ssa. ssa. subst. ssa.
  de i0. de o. de i2. de o. subst. de p. de o.
  de p1. de o. destruct H3. ssa. subst. de o0. de o1. de o1.
  subst. de o0. de o1. de o1. de p1. de o. de o0. de o1. de o1.
  de i2. de o. de p. de o. de p0. de o. destruct H3. ssa. subst.
  de o0. de o1. de o1. subst. de o0. de o1. de o1. de p0. de o. de o0.
  de o1. de o1. ssa.
(*  apply rel_eqpair_R2.   
  apply rel_eqpair_R2' in H. destruct H. left. split_and. right.
  split_and. ssa. ssa. destruct i0. ssa. destruct i2. ssa.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2. destruct H. left. split_and. eauto.
  apply rel_eqsum_L2' in H2.
  
(*  apply rel_eqsum_L' in H2.

  destruct i0. ssa.
  destruct i2. ssa. destruct H2. ssa. subst. left. con. eauto.
  de i3. de o0. de p. de o0. de o1. de o2. destruct H3. ssa. subst. destruct H4. split_and. de o.
  subst. ssa. destruct H4. subst. ssa. de o. subst. destruct H3. ssa. de o. de o2. subst.
  de o. de o. de o1. de o2. de o. subst. de o. de o2. subst. de o. de o. de p. de o0. de o1. de o2.
  de o. de o. de o2. de o. de o. de o1. de o2. de o. de o. de o. left. con. eauto.
  ssa. subst. de 
  apply rel_eqpair_R2' in H.

  destruct H. split_and.
  apply rel_eqsum_L2' in H2. con.*)
  destruct i0,i3,i2,i5.

  rewrite /map_pair /my_f_route.
  have: is_some i4 /\ is_some i6 \/ is_none i4 /\ is_none i6. de i4. de i6. de i6.

  case;split_and. destruct i4. 2:ssa. destruct i6. 2:ssa.
  rewrite /intermediate_outputRel in H2.
  apply rel_eqpair in H2. split_and.
  apply rel_eqpair in H5. split_and.
  rewrite !pair_rewr in H2 H5 H6. ssa.

  destruct i4. ssa. destruct i6. ssa.
  ssa.

(*  apply rel_eqsum_R2.
  apply rel_eqsum_LR.
  apply rel_eqmaybe_swi2 in H6. destruct H6. split_and. inversion H6. inversion H7. subst. done.
  destruct H6. split_and. ssa. split_and.
  destruct i4. ssa. destruct i6. ssa. simpl. left. con. eauto. done.
  split_and.

  apply rel_eqpair_R2. right. con.
  ssa. ssa.*)

  right. split_and. ssa. ssa.*)

  (*rewrite /map_pair /my_f_route. de i0. destruct i0. ssa. destruct i2. ssa.
  apply rel_eqpair_R2' in H. destruct H.
  apply rel_eqpair_R2. left. split_and. eauto.
  rewrite /my_f_route. destruct i0. destruct i3. destruct i2. destruct i5.
  apply rel_eqsum_R2' in H2. rewrite /intermediate_outputRel in H2.
  apply rel_eqpair in H2. split_and.
  rewrite !pair_rewr in H2 H3.
  apply rel_eqpair in H3. split_and. rewrite !pair_rewr in H3 H4.
  apply rel_eqmaybe_swi2 in H4. destruct H4. split_and. ssa.
  destruct H4. split_and. ssa.
  split_and. de i4. destruct i0. destruct i2. subst. de i3. de i5. ssa.
  de i6. de i5. de i6. de i3. de i2. de i3. de i5. de i6. de i6.de i6. de i6.

  split_and.

  rewrite /map_pair /my_f_route. destruct i0. destruct i3. destruct i2. destruct i5.
  ssa.*)
  
  (*case;split_and. destruct i4. 2:ssa. destruct i6. 2:ssa.
  rewrite /intermediate_outputRel in H2.
  apply rel_eqpair in H2. split_and.
  apply rel_eqpair in H5. split_and.
  rewrite !pair_rewr in H2 H5 H6.
  apply rel_eqpair_R2. left. con. eauto. ssa.
  destruct i4. ssa. destruct i6. ssa.
  apply rel_eqpair_R2. con. con. eauto. ssa. ssa.*)
(*  apply rel_eqsum_R2.
  apply rel_eqsum_LR.
  apply rel_eqmaybe_swi2 in H6. destruct H6. split_and. inversion H6. inversion H7. subst. done.
  destruct H6. split_and. ssa. split_and.
  destruct i4. ssa. destruct i6. ssa. simpl. left. con. eauto. done.
  split_and.

  apply rel_eqpair_R2. right. con.
  ssa. ssa.*)

  mrw. intros. destruct i. rewrite !pair_rewr.
  apply dis_eqpair_R in H.
  destruct i0. 2: ssa.
  apply dis_eqsum_L2 in H.
  destruct i0. ssa.
(*  apply dis_eqsum_R2 in H.
  apply dis_eqpair_R2.
  apply dis_eqmaybe2.
  apply dis_eqsum_R. done.*)

  mrw. intros.
  apply rel_eqsum_L2. eauto.

(*  move: H. instantiate (1:= publicRel _). (*because conclusion relates inr by eqsum_L*)
  intros. simpl in H. subst.
  apply rel_eqsum
  simpl in H. subst. ssa. ssa. ssa.
  destruct i4. ssa. destruct i6. ssa.
  simpl in H. subst. ssa.
  split_and.
  ssa.

  mrw. intros. ssa. de i. de s.

  mrw. intros.
  apply rel_eqsum_L2. eauto.*)

  rewrite /scheduled_process_pool.
  rewrite /nat_rec. rewrite /nat_rect.

  eapply par_NI.
  eapply map_NI.
  instantiate (1:= eqpair_R (publicRel _) (publicRel _)). 
  mrw. intros.
  ssa. left. destruct H. split_and. rewrite H. destruct H0. split_and.
  ssa. destruct H0. ssa. ssa. ssa. rewrite H H0 H1. done. rewrite H0 H1. done.
  
(*  destruct H. left. split_and. ssa. destruct H0. ssa. rewrite H H0 //.
  ssa. rewrite H H0 //. ssa. destruct H0. ssa. ssa.
  right. ssa.
  simpl in H. rewrite H. ssa. de i. de i'. subst. de p. de o. de p0. de o. de H0. de H0. de H0.
  split_and. ssa. left. rewrite H H0. ssa.
  de o. split_and.
  apply rel_eqpair_R2. right. 
  ssa. de i. de p. de o. de i'. de p0. de o.
  destruct H1. ssa. subst. auto. de p0. de o. de o0. de o1.
  destruct H2. ssa. subst. ssa. de o1. simpl.
  (*  apply rel_eqpair_R2. left. con. apply rel_refl.*)

(*  destruct H0. split_and. clear H1.
  apply rel_eqpair_R2.
  left. simpl. ssa. de i. de i'. subst. de p. de o. de p0. de o. subst.*)
  destruct (eqVneq l \bot). auto. left. ssa. left.
  ssa. intro. subst. rewrite eqxx in i. done.
  de p0. de o. de p. de o. de p0. de o. destruct H1. ssa. subst. de o0.
  de p0. de o. de o0. de o1. destruct H2. ssa. subst. auto.
  de o1. 
  destruct (eqVneq l \bot). auto. left. ssa. left. ssa. intro. subst. rewrite eqxx in i. done.

  split_and.
  ssa. de i. de p. de o. (*Yes! Here it worked because we used eqmaybe_top in public input structure*)*)

(*  done. de p0. de o.
  rewrite -H.
  
  instantiate (1:= (eqmaybe_top (publicRel Unit))).

  destruct H. split_and. simpl in H.

  
  left. con. rewrite /my_f_sch. instantiate (1:= publicRel _). rewrite H. apply rel_refl.
  destruct i. destruct i'. rewrite /option_inl_some !pair_rewr. rewrite !pair_rewr in H0.
  rewrite !pair_rewr in H. subst.
  apply rel_eqpair_R2' in H0.
  destruct H0. split_and. 
  

  split_and. apply dis_dis_rel. destruct i0. ssa.*)
(*  destruct x. destruct x0. instantiate (1:= eqmaybe _). apply rel_eqmaybe.
  apply rel_eqsum_R' in H2.
  apply rel_
  split_and.*)
  mrw. intros. de i. de i0. de p. de o0. de o1. subst.
  apply f_NI_id. 

  eapply NI_I_imp. instantiate (1:= eqpair_LR (publicRel Bool) (eqmaybe (publicRel Unit))).
  simpl. intros. de x. de o.
  instantiate (1:= (eqpair_LR (publicRel Bool)
                      (eqmaybe (eqsum_R (publicRel Unit) (eqsum_LR (semiprivateRel THandlerOutput) (semiprivateRel TInterrupt)))))).
  intros.
  ssa. de x. de o. de s. de s.
  intros. ssa. de H. de x. de o. de s. de s. de H. de x. de o. de s. de s. de y. de o. subst.
  de s. de s. subst. de y. de o. de s. de s.*)

  1: { 

  apply swi_NI. Check swi_NI. 
  intros.
  destruct (eqVneq l \bot). subst.
  right.

  pcofix CIH. pfold. con. intros.

  match_dd_o. intros.  de i0. inv x.
  destruct i0. have: Nothing == Notify = false. done. move=>->. eauto.
  rewrite eqxx.
  left. pcofix CIH2.
  pfold. con. intros.
  match_dd_o.

  intros. match_dd_o. con. eauto. ssa.
  intros. con. match_dd_o. ssa.
  left. rewrite /aware. intros. simpl in H. destruct H. ssa. subst. rewrite eqxx in i. done.

  eapply NI_I_imp.
  3: apply maybe_NI.
  intros. apply dis_eqmaybe in H. split_and. subst.
  apply dis_eqmaybe_false2. eauto.
  ssa. de x. de y. de y.

  eapply map_NI.
  mrw. intros.
  4: apply maybe_NI.
  destruct (eqVneq l \bot). subst. destruct i. destruct i'. rewrite /inl_some.
  apply rel_eqmaybe_top2. apply rel_eqsum_LR' in H. eauto. ssa.
  destruct i'. ssa. ssa.
  ssa. de i. de i'. de i'.

  mrw. intros. de i.

  mrw. intros. apply rel_eqpair_LR2. con. apply rel_refl. eauto.
  simpl. rewrite /high_p2. rewrite /alternate_generic2.

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
  shelve.
  
  eapply map_NI.
  apply f_NI_id.
  apply f_PU_id.

  mrw. intros. apply rel_eqsum_L2. eauto.

  apply sta_NI.
  mrw. intros. eauto.
  mrw. intros.
  destruct i. destruct i'. apply rel_eqsum_L' in H.
  instantiate (1:= semiprivateRel _). ssa. de H. de H0. subst. left. ssa.
  ssa. destruct i'. ssa. apply rel_refl.
  mrw. intros. destruct i. apply dis_eqsum_L2 in H. ssa. ssa.
  apply out_NI.
  
  Unshelve.
  2: { mrw. intros. ssa. } *)


}



  

  (*next process*)
  eapply map_NI.
  mrw. intros. rewrite /map_pair. destruct i,i'.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2.
  destruct H. split_and. 
  left. con. eauto.
  apply rel_eqmaybe2 in H0. destruct H0. split_and. subst.
  instantiate (1:=  (eqmaybe (eqsum_LR (semiprivateRel THandlerOutput) (semiprivateRel TInterrupt)))).
  destruct x. destruct x0. ssa. ssa. destruct x0. ssa.
  apply rel_eqmaybe. ssa. split_and. subst. ssa. split_and.
  right. con. ssa. de i0. de s. de i2. de i2.
  mrw. intros. ssa. de i. de o. de s.
  apply f_NI_id.

  apply par_NI.

  eapply map_NI.
  instantiate (1:= eqpair_R _ _).
  mrw. intros.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2.
  destruct H. split_and. 
  left. con. rewrite /my_f_sch. instantiate (1:= semiprivateRel _). rewrite H. apply rel_refl. eauto.
  split_and.
  mrw. intros. ssa.
  apply f_NI_id.

  eapply NI_I_imp.
  instantiate (1:= (eqpair_LR (semiprivateRel Bool)
                      (eqmaybe ((eqsum_LR (semiprivateRel THandlerOutput) (semiprivateRel TInterrupt)))))).
  ssa. de x. de o. de s.
  ssa. de H. de x. de o. de s. de H. de x. de o. de s. subst. de y. de o. de s. subst.
  de y. de o. de s.


  apply swi_NI.
  intros.
  destruct (eqVneq l \bot). subst.
  right.

  pcofix CIH. pfold. con. intros.

  match_dd_o.  de i0. inv x.
  destruct i0. have: Nothing == Notify = false. done. move=>->. eauto.
  rewrite eqxx.
  left. pcofix CIH2.
  pfold. con. intros.
  match_dd_o.

  intros. match_dd_o. con. eauto. ssa.
  intros. con. match_dd_o. ssa.
  left. rewrite /aware. intros. simpl in H. destruct H. ssa. subst. rewrite eqxx in i. done.

  eapply NI_I_imp.
  3: apply maybe_NI.
  intros. apply dis_eqmaybe in H. split_and. subst.
  apply dis_eqmaybe_false2. eauto.
  ssa. de x. de y. de y.

  eapply map_NI.
  mrw. intros.
  4: apply maybe_NI.
  destruct (eqVneq l \bot). subst. destruct i. destruct i'. rewrite /inl_some.
  apply rel_eqmaybe_top2. apply rel_eqsum_LR' in H. eauto. ssa.
  destruct i'. ssa. ssa.
  ssa. de i. de i'. de i'.

  mrw. intros. de i.

  mrw. intros. apply rel_eqpair_LR2. con. apply rel_refl. eauto.
  simpl. rewrite /high_p2. rewrite /alternate_generic2.

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
  shelve.
  
  eapply map_NI.
  apply f_NI_id.
  apply f_PU_id.

  mrw. intros. apply rel_eqsum_L2. eauto.

  apply sta_NI.
  mrw. intros. eauto.
  mrw. intros.
  destruct i. destruct i'. apply rel_eqsum_L' in H.
  instantiate (1:= semiprivateRel _). ssa. de H. de H0. subst. left. ssa.
  ssa. destruct i'. ssa. apply rel_refl.
  mrw. intros. destruct i. apply dis_eqsum_L2 in H. ssa. ssa.
  apply out_NI.
  
  Unshelve.
  2: { mrw. intros. ssa. } 

  (*final process*)
  fold interp.
  eapply map_NI.
  mrw. intros. rewrite /map_pair. destruct i,i'.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2.
  destruct H. split_and. 
  left. con. eauto.
  apply rel_eqmaybe2 in H0. destruct H0. split_and. subst.
  instantiate (1:=  (eqmaybe_top ((semiprivateRel TInterrupt)))). (*eqmaybe_top instead of eqmaybe*)
  destruct x. destruct x0. ssa. ssa. destruct x0. ssa.
  apply rel_eqmaybe. ssa. split_and. subst. ssa. split_and.
  right. con. ssa. de i0. de s. de i2. de i2.
  mrw. intros. ssa. de i. de o. de s.
  apply f_NI_id.

  eapply map_NI.
  instantiate (1:= eqpair_R _ _).
  mrw. intros.
  apply rel_eqpair_R2' in H.
  apply rel_eqpair_R2.
  destruct H. split_and. 
  left. con. rewrite /my_f_sch. instantiate (1:= semiprivateRel _). simpl in H. rewrite H. apply rel_refl. eauto.
  split_and.
  mrw. intros. ssa.
  apply f_NI_id.

  eapply NI_I_imp.
  instantiate (1:= (eqpair_LR (semiprivateRel Bool)
                      (eqmaybe_false (((semiprivateRel TInterrupt)))))). (*eqmaybe_false was necessary here, do we need it in the high proc too???*)
  ssa. de x. de o. de x. de o.

  ssa. de H. de x. de o.
  de H. de H. subst. de x. de o. de y. de o. subst. de y. de o. subst.
  de x. de o. de y. de o. de y. de o. de x. de y. de o. de o0. de o0.

  simpl. rewrite /handler. Check swi_NI.
  apply swi_NI.
  intros.
  destruct (eqVneq l \bot). subst.
  right.

  pcofix CIH. pfold. con. intros.

  match_dd_o. left. pcofix CIH2.
  pfold. con.
  intros. match_dd_o.
  intros. match_dd_o. con. eauto. ssa.

  intros. match_dd_o. con. eauto. ssa.
  intros. 
  left. rewrite /aware. intros. simpl in H. destruct H. ssa. subst. rewrite eqxx in i. done.

  eapply NI_I_imp.
  3: apply maybe_NI.
  intros. eauto.

  intros. done.



  eapply map_NI.
  apply f_NI_id.
  apply f_PU_id.
  
  (*Why could we just remove this chunk in the final part???*)  
  (*mrw. intros.
  4: apply maybe_NI.
  destruct (eqVneq l \bot). subst. destruct i. destruct i'. rewrite /inl_some.
  apply rel_eqmaybe_top2. apply rel_eqsum_LR' in H. eauto. ssa.
  destruct i'. ssa. ssa.
  ssa. de i. de i'. de i'.

  mrw. intros. de i. *)


  mrw. intros. apply rel_eqpair_LR2. con. apply rel_refl. eauto.
  simpl. rewrite /alternate_generic.

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
  shelve.
  
  eapply map_NI.
  apply f_NI_id.
  apply f_PU_id.  
  mrw. intros. apply rel_eqsum_L2. eauto.

  apply sta_NI.
  mrw. intros. eauto.
  mrw. intros.
  destruct i. destruct i'. apply rel_refl. ssa.
  destruct i'. ssa. apply rel_refl.
(*  apply rel_eqsum_L' in H.
  instantiate (1:= semiprivateRel _). ssa. de H. de H0. subst. left. ssa.
  ssa. destruct i'. ssa. apply rel_refl.*)
  mrw. intros. destruct i. apply dis_eqsum_L2 in H. ssa.
  instantiate (1:= semiprivateRel _). ssa. ssa.
  apply out_NI.
  apply rel_eqpair in H. split_and. rewrite !pair_rewr in H H0.
  ssa. destruct H. ssa. subst. left. ssa. auto.
  apply publicRel.
  
  Unshelve.
  apply rel_eqpair in H. split_and. rewrite !pair_rewr in H H0. ssa. destruct H. ssa. subst. eauto. auto.
  apply publicRel.
Qed.
















  



  
  simpl in H. destruct i,i'. rewrite !pair_rewr in H. subst.
  rewrite !pair_rewr in H0.
  rewrite !pair_rewr.
  apply rel_eqmaybe2 in H0.
  destruct H0. split_and. subst. 
  
  apply rel_eqpair_LR2. con.
  apply rel_eqmaybe. eauto.
  apply rel_eqmaybe. eauto.
  split_and;subst. ssa.
  split_and.
  apply rel_eqpair_LR2. con. ssa.
  apply dis_dis_rel. done. done.

  destruct i,i'.
  rewrite !pair_rewr in H,H0.
  rewrite !pair_rewr.
  apply dis_dis_rel. ssa.
  have: i0 <> None. de i0.
  intros. have: i2 <> None by de i2.
  intros.
  destruct i0.
  ssa. de s. de s. de i2. de s. de s. 
  destruct i2. simpl. de s. de s
  apply rel_eqpair_LR2. con. ssa.
  mrw. ssa.
  apply f_NI_id.

  Check swi_NI.
  eapply map_NI.
  left. con. ssa.
  apply rel_eqmaybe. eauto.
  right. ssa.
  ssa.
  
  de i'. de i'.
  de i. de i'. de i'. de i'.  
      destruct H.
  - split_ando. 
    apply rel_eqpair_OR in H0.
    destruct H0.
    * split_and. (*rel*)
      apply rel_eqmaybe_top in H;simpl in H.
      destruct H.
      ** split_and;subst. (*Some,Some*)
         apply rel_eqmaybe2 in H0;simpl in H0.
         destruct H0.
         *** split_and. subst.
             destruct H2;subst.
             **** apply rel_eqmaybe2 in H1;simpl in H1.
                  destruct H1. split_and.
             **** destruct H.
                  ***** split_and.
                  ***** split_and.
         *** apply rel_eqmaybe2 in H1;simpl in H1.
             destruct H1. 
             **** split_and.
             **** split_and.
      ** destruct H. (*Some,None*)
         *** split_and. subst.
             apply rel_eqmaybe2 in H1;simpl in H1.
             destruct H1.
             **** split_and. subst.
                  de H1.
             **** destruct H.
                  ***** split_and. subst.
                        rewrite /my_f_out. apply rel_eqmaybe_top_right.
                        apply dis_Some.

    * (*dis*)
  
  
Lemma main_NI : @NI _ _ (semiprivateRel _)
                  (eqmaybe (eqmaybe_top (eqsum_R (publicRel _) (semiprivateRel _))))
                  (@map _ _ _ (Option (Option (Sum TPublicOutput TTypeSyscall))) my_f_in my_f_out
                     (my_loop_and_count
                        (@scheduled_process_pool 2 my_f_I my_f_O (@my_f_sch my_f_I) my_procs))).
Proof.
  eapply map_NI.

  mrw. intros. rewrite /my_f_in.
  apply rel_eqsum_R2. apply rel_eqsum_R2. apply H.

  mrw. intros. rewrite /my_f_in. ssa.

  mrw. intros. move: H. instantiate (1:= eqpair_OR (eqmaybe_top (publicRel _)) (eqpair_OR (eqmaybe (semiprivateRel _)) (eqmaybe (semiprivateRel _)))).
  intros. 
  destruct i,i'. destruct i0,i2.

  apply rel_eqpair_OR in H.
    destruct H.
  - split_ando. 
    apply rel_eqpair_OR in H0.
    destruct H0.
    * split_and. (*rel*)
      apply rel_eqmaybe_top in H;simpl in H.
      destruct H.
      ** split_and;subst. (*Some,Some*)
         apply rel_eqmaybe2 in H0;simpl in H0.
         destruct H0.
         *** split_and. subst.
             destruct H2;subst.
             **** apply rel_eqmaybe2 in H1;simpl in H1.
                  destruct H1. split_and.
             **** destruct H.
                  ***** split_and.
                  ***** split_and.
         *** apply rel_eqmaybe2 in H1;simpl in H1.
             destruct H1. 
             **** split_and.
             **** split_and.
      ** destruct H. (*Some,None*)
         *** split_and. subst.
             apply rel_eqmaybe2 in H1;simpl in H1.
             destruct H1.
             **** split_and. subst.
                  de H1.
             **** destruct H.
                  ***** split_and. subst.
                        rewrite /my_f_out. apply rel_eqmaybe_top_right.
                        apply dis_Some.

    * (*dis*)

                  
        
  destruct H1. subst. ssa. ssa.
  destruct H. split_ando. subst. simpl. 
  
  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac. rewrite /my_f_out.
  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.

  
  move: H. instantiate (1:= eqpair_R (publicRel _) (eqpair_LR (eqmaybe_top (semiprivateRel _)) (eqmaybe_top (semiprivateRel _)))).
  intros. destruct i,i'.
  ssa.

                       

  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.

  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.  
  temp_tac.
  temp_tac.
  temp_tac.
  temp_tac.    
  destruct H. ssa. subst. destruct H0.
  de i0. de o. de i2. de o. de H. subst. de o0. de H1. de o1.
  de H. subst. de i1. de i1. de o1. de i1. de i1. de H1. de o1. de i1.
  de o1. subst. de i1. de i1. de o0. de H1. de o1. de H0. subst.
  de i1. subst. de i1. de o1. subst. de i1. de i1. de H1. de o1. subst.
  de i1. subst. de o1. subst. de i1. de i1. de H1. de i2. de o.
  de o0. de o1. de H0. subst. de i1. subst. de i1. de o1. de i1. de i2. de o. de o0.
  subst. de o1. de i1. de i1. de o1. subst. de i1. de i1. ssa.
  de i0. de o. de i2. de o. subst. de o0. de H
1  de o0.
  
  rewrite /my_f_out. destruct i. destruct i1.
  apply rel_eqmaybe.
  apply rel_eqsum_R. ssa.












  
(*Lemma rel_inl : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]), rel (eqsum_L ARel BRel) ((inl \o f) ) ()*)
(*Lemma eqsum_R2 : forall (A B B' : Ty) l (x y : [A] + [B]) (f : [B] -> [B']) (ARel : myrel [A]) (BRel : myrel [B]) (BRel' : myrel [B']),
    f_NI BRel BRel' f -> rel (eqsum_R ARel BRel) l x y -> rel (eqsum_R ARel BRel') l x (f y).*)
Lemma rel_eqsum_LR3 : forall (A B : Ty) (ARel : myrel [A]) (BRel : myrel [B]) l x y, rel (eqsum_LR ARel BRel) l x y -> (exists x' y', x = inl x' /\ y = inl y' /\ rel ARel l x' y') \/ (exists x' y', x = inr x' /\ y = inr y' /\ rel BRel l x' y') \/ (exists x' y', x = inl x' /\ y = inr y' /\ dis ARel l x' /\ dis BRel l y') \/  (exists x' y', x = inr x' /\ y = inl y' /\ dis BRel l x' /\ dis ARel l y').
Proof.
  intros. destruct x. destruct y. left. exists i. exists i0. con. auto. con. auto.
  apply rel_eqsum_LR' in H. done.
  right. right. left. exists i. exists i0. con. auto. con. auto.
  ssa.
  destruct y. right. right. right.
  exists i. exists i0. con. auto. con. auto. ssa.
  right. left. exists i. exists i0. con. auto. con. auto.
  apply rel_eqsum_LR2' in H. done.
Qed.

Lemma interp_eq : (fix interp (t : Ty) : Set :=
       match t with
       | Nat => nat
       | Times t0 t1 => (interp t0 * interp t1)%type
       | Bool => bool
       | Option t' => option (interp t')
       | Sum t0 t1 => (interp t0 + interp t1)%type
       | TInput => Input
       | TOutput => Output
       | TTypeSyscall => TypeSyscall
       | Unit => unit
       | TInterrupt => Interrupt
       | THandlerOutput => HandlerOutput
       | TPublicOutput => PublicOutput
       | TPublicInput => PublicInput
       end) = interp.
  done.
Qed.

Lemma rel_top_false : forall (A : Ty) (ARel : myrel [A])l x y, rel (eqmaybe_top ARel) l x y -> rel (eqmaybe_false ARel) l x y.
Proof.
  intros. ssa. de x. de H. de y. de H. de y.
Qed.  

  
Lemma NI_main : @NI _ _ InputRel' OutputRel' (mitigator2 process_pool2).
Proof.  
  rewr. 
  eapply (@map_NI _ _ _ _ _ _ _ _ LoopTypeRel LoopTypeRel). 
  
  mrw. intros. rewrite /comp. apply rel_eqsum_LR. 
  de i. de i'. de i'. de H. subst. auto.

  mrw. ssa. de i.

  mrw. intros. rewrite /collapse_in_out.
  de i. de i'. de i. de p. de o. de i'. de i'. de i. de o. de i'.
  
  apply loop_NI.

  eapply map_NI.

  mrw. intros.
  instantiate (1:= eqsum_LR InterRel (semiprivateRel _)).
  de i. de i'. de i'.

  mrw. intros. de i.

  instantiate (1:= eqpair _ _). mrw. intros.
  destruct i,i'.
  rewrite !pair_rewr.
  apply rel_eqpair in H. destruct H.
  eauto.
  
  eapply sta_NI.

  mrw. intros.
  instantiate (1:= publicRel _). ssa. (*public rel for state*)

  mrw. intros. done.

  mrw. intros. done.

  eapply map_NI.

  instantiate (1:= eqmaybe_false (eqmaybe_false InterRel)).
  mrw. intros. destruct i,i'.
  rewrite !pair_rewr.
  apply rel_eqpair_R2' in H.
  destruct H. destruct H.

  apply rel_eqsum_LR3 in H0.
  destruct H0. destruct H0. destruct H0.
  destruct H0. destruct H1. subst.
  have: i = i1. ssa. move=>->.
  have: is_inr x = is_inr x0. de x. de x0. de x0.
  move=>->.
  case_if.
  apply/rel_eqmaybe.
  apply/rel_eqmaybe.
  done.
  ssa.
  destruct H0.
  destruct H0. destruct H0. destruct H0. destruct H1.
  subst.
  have: i = i1. ssa. move=>->.
  case_if. apply/rel_eqmaybe. ssa. ssa.

  destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
  destruct H2. subst.
  have: i = i1. ssa. move=>->.
  apply/dis_dis_rel. case_if. ssa. ssa.
  case_if. ssa. ssa.
  destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
  subst.
  apply/dis_dis_rel. case_if. done. done.
  case_if. done. done.
  destruct H.
  destruct i0. destruct i2.
  destruct i0. ssa.
  destruct i2. ssa.
  rewrite /is_inr orbC. rewrite /orb.
  case_if. apply dis_dis_rel. done. done. 
  move: H1. case_if. done. done.
  destruct i0. ssa. rewrite /is_inr orbC /orb.
  apply dis_dis_rel. done. case_if. done. done.
  destruct i2. destruct i2. ssa.
  rewrite /is_inr orbC /orb. case_if.
  apply dis_dis_rel. done. done.
  apply dis_dis_rel. done. ssa.
  apply dis_dis_rel.
  case_if. done. done.
  case_if. done. done.

  mrw. intros. destruct i. rewrite pair_rewr.
  apply dis_eqpair_R in H.
  destruct i0. destruct i0. ssa. rewrite !pair_rewr.
  rewrite /is_inr orbC /orb. ssa.
  destruct i0. rewrite pair_rewr.
  case_if. ssa. ssa.

  instantiate (1:= OutputRel').
  mrw. intros. auto.

(*  eapply NI_I_imp.
  instantiate (1:= eqmaybe_false (eqmaybe_false InterRel)). ssa.
  de x.
  intros. apply rel_top_false. done.*)

  apply maybe_NI.

  eapply map_NI.

  instantiate (1:= eqpair_LR boolRel (eqmaybe_false InterRel)).
  mrw. intros.

  de i. de i'. de H. de i. de H. de i'. de i'. de s.

  mrw. intros. de i. de i.

  

(*  Check par_NI.
  
  apply swi_NI. shelve.

  apply maybe_NI.

  2: { apply swi_NI. shelve. apply maybe_NI. shelve. }

  Unshelve.

  2: { mrw. intros.
       instantiate (1:= InterRel).
       instantiate (1:= privateRel _). ssa. } 


  instantiate (1:= eqpair_LR (publicRel _) (eqmaybe_top InterRel)). (*None maps to true, so we make the whole bool private to preserve from None*) (*problem in oblivious/output case, now trying publicRel*)
  mrw. intros.
  destruct i. destruct i'.
  apply rel_eqpair_LR2. con. ssa. done.
  ssa. de H. de i. (*Something interesting happened here, worried this would not be true*)
  destruct i'.
  ssa. de H. de i. ssa.

  mrw. intros. de i. de i. de (eqVneq l \bot). exfalso. apply/H.
  apply/eqP. done.*)

  apply f_NI_id.

  eapply NI_O_imp.
  instantiate (1:= eqpair _ _).
  intros. apply rel_eqpair in H. destruct H.
  destruct x. destruct y.
(*  Search _ (rel (eqpair_R _ _)).*)
  apply rel_eqpair_LR2. (*Since switch to *_LR. MAYBE WRONG*)
  rewrite !pair_rewr in H H0.
  con. eauto. eauto.

  apply par_NI.

  apply swi_NI.

  intros.
  right.

  left. rewrite /aware. intros. simpl in H. de H. subst.
  intro.
  de (eqVneq l \bot). subst. right.

  pcofix CIH.
  pfold. con. 
  intros;match_dd_once;eauto.
  match_dd_once. match_dd_once.
  right. eauto. rewrite /inl_some in x. de i0.
  match_dd. left. pcofix CIH2. pfold. con.
  intros.
  match_dd_once. eauto.
  match_dd_once. match_dd_once.
  right. eauto.
  match_dd. right. eauto.
  
  intros.
  match_dd. con. admit. simpl.
  
  move: CIH. rewrite /alternate_generic2.
  left. pfold. con. intros. match_dd_once.
  admit. 
  right. eauto.
  intros;match_dd_once;eauto;left;pfold;con.  
  match_dd_once. left.
  pfold. con. intros.
  match_dd_once. left.
  pfold. con. intros.
  match_dd_once. left.
  pfold. con. intros.
  match_dd_once.
  left. rewrite /aware. intros. simpl in H. destruct H. ssa.
  intro. apply/negP. apply i. apply/eqP. done. move/eqP : H.
  move/negbTE : i. move=>->. done.

