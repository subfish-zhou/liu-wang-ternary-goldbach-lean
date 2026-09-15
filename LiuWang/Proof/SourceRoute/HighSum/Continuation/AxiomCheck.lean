import LiuWang.Proof.SourceRoute.HighSum.Continuation.Residual
import LiuWang.Proof.SourceRoute.HighSum.Continuation.EndpointScalar

set_option autoImplicit false

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation

#print axioms lambdaCountIntegrand
#print axioms lambdaCountSegment
#print axioms source31Profile
#print axioms original_table_domain
#print axioms original_familyCount_row
#print axioms lambdaCountIntegrand_integrable
#print axioms lambdaCountSegment_le_row
#print axioms lambdaCountSegment_split
#print axioms actual_source31_slice
#print axioms actual_source31_alpha_slice
#print axioms source31Window
#print axioms source31Window_measurable
#print axioms original_source31_endpoints
#print axioms integral_Ioc_indicator
#print axioms source31Window_slice
#print axioms actual_source31_height_integrable
#print axioms source31Profile_continuousOn
#print axioms source31_height_majorant_integrable
#print axioms actual_source31_full_height
#print axioms source31Profile_nonneg
#print axioms source31_log_integrand_continuousOn
#print axioms source31_log_integrand_integrable
#print axioms source31_log_substitution
#print axioms original_log_height_bounds
#print axioms actual_source31_log_height
#print axioms actual_source31
#print axioms unpaidAlpha
#print axioms unpaidAlpha_eq_original_ranges
#print axioms unpaidAlpha_nonneg
#print axioms original_alpha_height_integrable
#print axioms unpaidHeight_integrable
#print axioms original_height_eq_unpaid_add_table
#print axioms highSum_le_unpaid_add_source31
#print axioms log_3100_bounds
#print axioms original_log_linear
#print axioms endpoint_root_certificates
#print axioms endpoint_log_power
#print axioms endpoint_denominator
#print axioms endpoint_first_normalized
#print axioms endpoint_second_normalized
#print axioms original_source21_scalar

#check actual_source31
#check highSum_le_unpaid_add_source31
#check original_source21_scalar

open NearOneDensity in
example : (rowBound .r039, rowBound .r042, rowBound .r045, rowBound .r046,
    rowBound .r047, rowBound .r0475, rowBound .r0478) =
    (35, 89, 182, 292, 664, 1668, 14000) := rfl

end LiuWang.Proof.SourceRoute.HighSum.Continuation
