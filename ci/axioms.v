(* The assumptions of the paper's results.  CI fails if any of them depends on
   anything beyond the two parameters that fix the security lattice,
   definitions.d and definitions.L. *)
From NonInterference.theories Require Import theorems concrete_system model_immediate model_sliced model_timer_unmasked noninterference adequacy.

Print Assumptions out_NI.
Print Assumptions map_NI.
Print Assumptions sta_NI.
Print Assumptions sta_NI_pred.
Print Assumptions swi_NI.
Print Assumptions par_NI.
Print Assumptions loop_NI.
Print Assumptions maybe_NI.
Print Assumptions model_immediate_not_NI.
Print Assumptions model_immediate_userview_not_NI.
Print Assumptions model_immediate_publicview_not_NI.
Print Assumptions model_policy_NI.
Print Assumptions model_sliced_NI.
Print Assumptions model_sliced_userview_NI.
Print Assumptions model_timer_unmasked_NI.
Print Assumptions trace_timer_in_slice'.
Print Assumptions sliced_run_gated.
Print Assumptions run_states_model.
Print Assumptions NI_paper.
Print Assumptions ObliviousDis_iff.
Print Assumptions NI_lEquiv.
Print Assumptions model_immediate_not_NI_paper.
Print Assumptions model_sliced_NI_paper.
