import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.RealTail
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.DensityDomainCheck

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

#print sourceCutoff
#print sourceNu
#print sourceM6
#print m6LogKernel
#print m6OriginalScalar
#print sourceM5
#print sourceHighRealTail

#check @sourceCutoff_order
#check @moving_countIntegral_monotone
#check @moving_strip_integrable
#check @moving_countIntegral_split
#check @moving_14000_strip_bound
#check @moving_cutoff_exp_continuous
#check @moving_14000_height_bound
#check @cutoff_exp_log_substitution
#check @sourceM6_same_modulus
#check @m6LogKernel_integrable
#check @equation_5_44_original_integral
#check @source_reciprocal_rounding
#check @source_local_region_parameters
#check @bandValues_nonreal
#check @familyCount_above_local_cutoff_eq_real
#check @local_tail_integral_eq_real
#check @equation_5_42_with_real_tail
#check @sigma6_original_reduction_with_real_tail
#check @log_3100_ge_eight
#check @original_scalar_density_domain_failure
#check @sourceL_ceil_exp_3100
#check @original_integer_density_domain_failure

#print axioms sourceCutoff
#print axioms sourceNu
#print axioms sourceM6
#print axioms m6LogKernel
#print axioms m6OriginalScalar
#print axioms sourceM5
#print axioms sourceHighRealTail
#print axioms sourceCutoff_order
#print axioms moving_countIntegral_monotone
#print axioms moving_strip_integrable
#print axioms moving_countIntegral_split
#print axioms moving_14000_strip_bound
#print axioms moving_cutoff_exp_continuous
#print axioms moving_14000_height_bound
#print axioms cutoff_exp_log_substitution
#print axioms sourceM6_same_modulus
#print axioms m6LogKernel_integrable
#print axioms equation_5_44_original_integral
#print axioms source_reciprocal_rounding
#print axioms source_local_region_parameters
#print axioms bandValues_nonreal
#print axioms familyCount_above_local_cutoff_eq_real
#print axioms local_tail_integral_eq_real
#print axioms equation_5_42_with_real_tail
#print axioms sigma6_original_reduction_with_real_tail
#print axioms log_3100_ge_eight
#print axioms original_scalar_density_domain_failure
#print axioms sourceL_ceil_exp_3100
#print axioms original_integer_density_domain_failure

#check @M3_near_one_integral_paid
#check @sigma6_low_and_endpoint_paid
#print axioms M3_near_one_integral_paid
#print axioms sigma6_low_and_endpoint_paid

example (L : ℝ) :
    m6OriginalScalar L =
      70000 * L ^ 4 *
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (L ^ 6)) +
          2.50637 / Real.log (Real.log (L ^ 6))) *
        ∫ t in Real.log (10 * Real.pi * L ^ 7)..Real.log (L ^ 21),
          Real.exp (-t - 0.10367089 * L / t) := rfl

example (q : ℕ) [NeZero q] (X y d : ℝ) :
    countIntegral q X y (sourceCutoff q d y) (sourceCutoff q d y) = 0 := by
  simp only [countIntegral, intervalIntegral.integral_same]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
