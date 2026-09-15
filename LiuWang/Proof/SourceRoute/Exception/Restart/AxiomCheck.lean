import LiuWang.Proof.SourceRoute.Exception.Restart.MovingHeight
import LiuWang.Proof.SourceRoute.Exception.Restart.Multiplicity
import LiuWang.Proof.SourceRoute.Exception.Restart.PaperApplication

set_option autoImplicit false

namespace LiuWang.Proof.SourceRoute.Exception.Restart

#print axioms realTerm
#print axioms realTerm_eq
#print axioms realTerm_hasSum
#print axioms fourWeight
#print axioms fourWeight_eq
#print axioms fourWeight_nonneg
#print axioms fourWeight_antitone
#print axioms four_factor_stechkin_nonneg
#print axioms distinct_sources_damped_bound
#print axioms real_sources_unique_eight
#print axioms original_re_half
#print axioms real_sources_unique_original
#print axioms two_zero_budget_contradiction
#print axioms induced_inverse
#print axioms pair_principal_forces_induction
#print axioms primitive_pair_nonprincipal_of_not_induced
#print axioms mixed_sources_damped_bound
#print axioms mixed_sources_exclusion
#print axioms damped_inverse_neg
#print axioms original_gap_scaled
#print axioms quadratic_low_original
#print axioms same_source_damped_bound
#print axioms fixed_source_nonreal_exclusion
#print axioms source_zeta_damped_bound
#print axioms fixed_source_zeta_exclusion
#print axioms induced_source_zero
#print axioms primitive_induction_trans
#print axioms fixed_source_nonprincipal_induced
#print axioms original_gap_at_conductor
#print axioms fixed_source_characterization
#print axioms fixed_source_zero_iff
#print axioms fixed_source_noninducing_no_zero
#print axioms original_seed_lifetime
#print axioms moving_fixed_source_characterization
#print axioms moving_noninducing_no_zero
#print axioms originalZeroSlots
#print axioms fixed_source_slots_subsingleton
#print axioms fixed_source_slots_nonempty_iff
#print axioms paper_source_original_zero_iff
#print axioms paper_source_original_noninducing_no_zero

#check @real_sources_unique_original
#check @mixed_sources_damped_bound
#check @quadratic_low_original
#check @fixed_source_characterization
#check @fixed_source_zero_iff
#check @fixed_source_noninducing_no_zero
#check @original_seed_lifetime
#check @moving_fixed_source_characterization
#check @moving_noninducing_no_zero
#check @originalZeroSlots
#check @fixed_source_slots_subsingleton
#check @fixed_source_slots_nonempty_iff
#check @paper_source_original_zero_iff
#check @paper_source_original_noninducing_no_zero

end LiuWang.Proof.SourceRoute.Exception.Restart
