import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Reduction

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate

theorem original_kernel_exponent_bound {L t : ℝ} (hL : 3100 ≤ L) (ht : 0 < t) :
    -t - 0.10367089 * L / t ≤ -(9 / 10 : ℝ) * t - 11.3 := by
  have h : 11.3 - t / 10 ≤ 0.10367089 * L / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith [sq_nonneg (t - 56.5)]
  linarith

theorem integral_affine_exponential (a b : ℝ) :
    (∫ t in a..b, Real.exp (-(9 / 10 : ℝ) * t - 11.3)) =
      (10 / 9 : ℝ) * Real.exp (-11.3) *
        (Real.exp (-(9 / 10 : ℝ) * a) - Real.exp (-(9 / 10 : ℝ) * b)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (f := fun t => -(10 / 9 : ℝ) * Real.exp (-(9 / 10 : ℝ) * t - 11.3))
    (f' := fun t => Real.exp (-(9 / 10 : ℝ) * t - 11.3))
    (fun t _ => by
      have hd := ((((hasDerivAt_id t).const_mul (-(9 / 10 : ℝ))).sub_const 11.3).exp.const_mul
        (-(10 / 9 : ℝ)))
      simp only [id_eq] at hd
      convert hd using 1
      · rfl
      · ring)
    ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub continuous_const)).intervalIntegrable a b)
  rw [h, Real.exp_sub, Real.exp_sub, Real.exp_neg]
  ring

theorem original_finite_integral_certificate {L a b : ℝ}
    (hL : 3100 ≤ L) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, m6LogKernel L t) ≤
      (10 / 9 : ℝ) * Real.exp (-11.3) *
        (Real.exp (-(9 / 10 : ℝ) * a) - Real.exp (-(9 / 10 : ℝ) * b)) := by
  rw [← integral_affine_exponential]
  apply intervalIntegral.integral_mono_on hab (m6LogKernel_integrable ha hab)
    ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub continuous_const)).intervalIntegrable a b)
  intro t ht
  exact Real.exp_le_exp.mpr (original_kernel_exponent_bound hL (ha.trans_le ht.1))

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate
