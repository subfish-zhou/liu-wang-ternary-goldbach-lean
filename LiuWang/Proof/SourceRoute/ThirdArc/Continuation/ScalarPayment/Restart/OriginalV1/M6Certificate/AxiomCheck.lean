import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.Payment

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate

#check @log_ten_pi_bounds
#check @exp_euler_le_two
#check @source_loglog_bounds
#check @sourceNu_sixth_bounds
#check @original_log_interval
#check @endpoint_rational_certificate
#check @original_kernel_exponent_bound
#check @integral_affine_exponential
#check @original_finite_integral_certificate
#check @original_finite_scalar_certificate
#check @original_scalar_global_reduction
#check @m6OriginalScalar_le
#check @equation_5_44_paid

#print axioms log_ten_pi_bounds
#print axioms exp_euler_le_two
#print axioms source_loglog_bounds
#print axioms sourceNu_sixth_bounds
#print axioms original_log_interval
#print axioms endpoint_rational_certificate
#print axioms original_kernel_exponent_bound
#print axioms integral_affine_exponential
#print axioms original_finite_integral_certificate
#print axioms original_finite_scalar_certificate
#print axioms original_scalar_global_reduction
#print axioms m6OriginalScalar_le
#print axioms equation_5_44_paid

#print m6OriginalScalar
#print m6LogKernel
#print sourceNu
#print sourceM6
#check @equation_5_44_original_integral
#print axioms equation_5_44_original_integral

example : ∀ L : ℝ, 3100 ≤ L →
    70000 * L ^ 4 *
      (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (L ^ 6)) +
        2.50637 / Real.log (Real.log (L ^ 6))) *
      (∫ t in Real.log (10 * Real.pi * L ^ 7)..Real.log (L ^ 21),
        Real.exp (-t - 0.10367089 * L / t)) ≤ 6 / 1000000000 :=
  m6OriginalScalar_le

example : m6OriginalScalar (3100 : ℝ) ≤ 6 / 1000000000 :=
  m6OriginalScalar_le 3100 le_rfl

example (a : ℝ) :
    (∫ t in a..a, Real.exp (-(9 / 10 : ℝ) * t - 11.3)) =
      (10 / 9 : ℝ) * Real.exp (-11.3) *
        (Real.exp (-(9 / 10 : ℝ) * a) - Real.exp (-(9 / 10 : ℝ) * a)) :=
  integral_affine_exponential a a

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate
