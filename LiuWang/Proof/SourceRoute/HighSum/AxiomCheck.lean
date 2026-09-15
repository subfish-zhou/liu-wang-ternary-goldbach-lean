import LiuWang.Proof.SourceRoute.HighSum.SourceReduction
import LiuWang.Proof.SourceRoute.HighSum.LambdaSegments

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum

#check sourceMass_le_full_height
#check original_highSum_le_density_integrals
#check original_source24_formula
#check original_source29
#check original_source30

#print axioms heightKernel
#print axioms heightKernel_integrable
#print axioms integral_heightKernel
#print axioms height_indicator_integrable
#print axioms integral_height_indicator
#print axioms zeroValues_height_filter
#print axioms count_height_integrand
#print axioms count_height_integrable
#print axioms integral_count_height
#print axioms count_height_identity
#print axioms band_reciprocal_le_height_integral
#print axioms family_height_integrable
#print axioms family_reciprocal_le_height_integral
#print axioms zeroValues_rectangle_filter
#print axioms count_rectangle_integrand
#print axioms count_rectangle_integrable
#print axioms family_rectangle_integrable
#print axioms family_height_alpha_swap
#print axioms family_height_alpha_integrable
#print axioms count_alpha_integrable
#print axioms family_alpha_integrable
#print axioms sourceMass_le_full_height
#print axioms original_height_alpha_swap
#print axioms original_excess_le_density_integrals
#print axioms original_highSum_le_density_integrals
#print axioms original_primed_le_density_integrals
#print axioms original_highPacket_le_density_integrals
#print axioms integral_exp_shift
#print axioms weighted_power_product
#print axioms sevenEnvelope
#print axioms continuous_sevenEnvelope
#print axioms sourceSeven_weighted_le_envelope
#print axioms integral_sevenEnvelope
#print axioms sourceSeven_integrand_integrable
#print axioms sourceSeven_integral_le_source24
#print axioms original_product_ge
#print axioms original_log_product_ge_ten
#print axioms original_density_rate_pos
#print axioms original_alpha_cutoff_mem
#print axioms log_density_ratio
#print axioms original_source24_formula
#print axioms actual_lambda_substitution
#print axioms original_source29
#print axioms original_alpha_split
#print axioms actual_lambda_integrable
#print axioms split_source30
#print axioms original_source30_integrable
#print axioms original_source30
#print axioms lambdaSegment
#print axioms lambdaSegment_eq
#print axioms lambdaSegment_eq_source_power
#print axioms source31_signed_segments
#print axioms source35_signed_segments

example {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (∫ y in u..T, (Set.Ici u).indicator heightKernel y) = 1 / u - 1 / T := by
  simpa only [max_self] using integral_height_indicator hu huT huT

example {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (∫ y in u..T, (Set.Ici T).indicator heightKernel y) = 0 := by
  simpa only [max_eq_right huT, sub_self] using integral_height_indicator hu huT le_rfl

example {u T t : ℝ} (hu : 0 < u) (huT : u ≤ T) (ht : t ≤ u) :
    (∫ y in u..T, (Set.Ici t).indicator heightKernel y) = 1 / u - 1 / T := by
  simpa only [max_eq_left ht] using integral_height_indicator hu huT (ht.trans huT)

end LiuWang.Proof.SourceRoute.HighSum
