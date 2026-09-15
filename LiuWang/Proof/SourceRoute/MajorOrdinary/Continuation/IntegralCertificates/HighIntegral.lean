import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.HighEndpoints

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates

theorem split_endpoint_mem : (100000 : ℝ) ≤ Real.exp 18 ∧ Real.exp 18 ≤ 10000000000 := by
  have hlog : Real.log (100000 : ℝ) ≤ 18 := by
    rw [show (100000 : ℝ) = (2 * 5) ^ 5 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  exact ⟨(Real.log_le_iff_le_exp (by norm_num)).mp hlog,
    (Real.le_log_iff_exp_le (by norm_num)).mp (by linarith [log_ten_billion_bounds.1])⟩

theorem high_integral_finite_reduction :
    (∫ x in (100000 : ℝ)..10000000000, nuKernel (7 / 6) x) ≤ (highRationalUpper : ℝ) := by
  have hs := split_endpoint_mem
  have hleft := kernel_integral_le_cubic (s := 7 / 6) (t := 16) (by norm_num)
    (A := 100000) le_rfl hs.1 (by norm_num)
  have hright := kernel_integral_le_cubic (s := 7 / 6) (t := 20) (by norm_num)
    hs.1 hs.2 (by norm_num)
  rw [show (7 / 6 - 1 : ℝ) = 1 / 6 by norm_num] at hleft hright
  have b0 := (cubicEndpointExpression 16).interval_correct firstLeft_contains
  have b1 := (cubicEndpointExpression 16).interval_correct firstRight_contains
  have b2 := (cubicEndpointExpression 20).interval_correct secondLeft_contains
  have b3 := (cubicEndpointExpression 20).interval_correct secondRight_contains
  have he16 (x : ℝ) := eval_cubicEndpointExpression 16 x
  have he20 (x : ℝ) := eval_cubicEndpointExpression 20 x
  norm_num only [Rat.cast_ofNat] at he16 he20
  rw [he16] at b0 b1
  rw [he20] at b2 b3
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (nuKernel_intervalIntegrable (7 / 6) le_rfl hs.1)
    (nuKernel_intervalIntegrable (7 / 6) hs.1 hs.2)]
  unfold highRationalUpper
  push_cast
  linarith only [hleft, hright, b0.1, b1.2, b2.1, b3.2]

theorem high_nuKernel_integral :
    (∫ x in (100000 : ℝ)..10000000000, nuKernel (7 / 6) x) ≤ 8794 :=
  high_integral_finite_reduction.trans (by exact_mod_cast highRationalUpper_le)

theorem original_high_fixed_integral :
    (∫ x in (100000 : ℝ)..10000000000, x ^ (-5 / 6 : ℝ) * nu x ^ 2) ≤ 8794 := by
  simpa only [nuKernel, show (7 / 6 - 2 : ℝ) = -5 / 6 by norm_num] using high_nuKernel_integral

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates
