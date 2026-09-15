import LiuWang.Proof.Campaign20260915.ZetaWinding.HadamardLogSum

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.DirichletZeroCount.Argument

theorem xiGenusLog_eq_zero_log {s : ℂ} (p : RiemannXiDivisorZeroIndex)
    (hs : s ≠ riemannXiDivisorZeroValue p) :
    xiGenusLog s p = Real.log ‖s - riemannXiDivisorZeroValue p‖ -
      Real.log ‖riemannXiDivisorZeroValue p‖ + (s / riemannXiDivisorZeroValue p).re := by
  have hp := riemannXiDivisorZeroValue_ne_zero p
  have he : 1 - s / riemannXiDivisorZeroValue p =
      -(s - riemannXiDivisorZeroValue p) / riemannXiDivisorZeroValue p := by
    field_simp
    ring
  unfold xiGenusLog weierstrassFactor
  rw [partialLogSum_eq_sum]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one]
  rw [norm_mul, Real.log_mul
    (norm_ne_zero_iff.mpr (by rw [he]; exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hs)) hp))
    (norm_ne_zero_iff.mpr (exp_ne_zero _)), norm_exp, Real.log_exp,
    he, norm_div, norm_neg, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs))
      (norm_ne_zero_iff.mpr hp)]

theorem integral_re_mul_horizontal (c : ℂ) (T a b : ℝ) :
    (∫ x in a..b, (horizontalAt T x * c).re) =
      (b ^ 2 - a ^ 2) / 2 * c.re - (b - a) * T * c.im := by
  have he : (fun x => (horizontalAt T x * c).re) =
      fun x : ℝ => x * c.re - T * c.im := by
    funext x
    simp [horizontalAt, mul_re]
  have hi : IntervalIntegrable (fun x : ℝ => x * c.re) volume a b :=
    (continuous_id.mul continuous_const).intervalIntegrable a b
  have hlin : (∫ x in a..b, x * c.re) = ((b ^ 2 - a ^ 2) / 2) * c.re := by
    simpa only [integral_id] using!
      (intervalIntegral.integral_mul_const (a := a) (b := b) (μ := volume)
        c.re (fun x : ℝ => x))
  rw [he, intervalIntegral.integral_sub hi intervalIntegrable_const, hlin,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem xiGenusLog_integral_eq_kernel (p : RiemannXiDivisorZeroIndex) (T a b : ℝ) :
    (∫ x in a..b, xiGenusLog (horizontalAt T x) p) =
      logNormPrimitive (T - (riemannXiDivisorZeroValue p).im)
        (b - (riemannXiDivisorZeroValue p).re) -
      logNormPrimitive (T - (riemannXiDivisorZeroValue p).im)
        (a - (riemannXiDivisorZeroValue p).re) -
      (b - a) * Real.log ‖riemannXiDivisorZeroValue p‖ +
      (b ^ 2 - a ^ 2) / 2 * ((riemannXiDivisorZeroValue p)⁻¹).re -
      (b - a) * T * ((riemannXiDivisorZeroValue p)⁻¹).im := by
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc a b →
      xiGenusLog (horizontalAt T x) p =
        Real.log ‖horizontalAt T x - riemannXiDivisorZeroValue p‖ -
          Real.log ‖riemannXiDivisorZeroValue p‖ +
            (horizontalAt T x * (riemannXiDivisorZeroValue p)⁻¹).re := by
    filter_upwards [volume.ae_ne (riemannXiDivisorZeroValue p).re] with x hx _
    have hn : horizontalAt T x ≠ riemannXiDivisorZeroValue p := by
      intro he
      exact hx (by simpa [horizontalAt] using congrArg Complex.re he)
    simpa only [div_eq_mul_inv] using xiGenusLog_eq_zero_log p hn
  have hi : IntervalIntegrable
      (fun x => (horizontalAt T x * (riemannXiDivisorZeroValue p)⁻¹).re) volume a b := by
    apply Continuous.intervalIntegrable
    unfold horizontalAt
    fun_prop
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_add
      ((log_norm_zero_factor_integrable (riemannXiDivisorZeroValue p) T a b).sub
        intervalIntegrable_const) hi,
    intervalIntegral.integral_sub (log_norm_zero_factor_integrable _ T a b) intervalIntegrable_const,
    integral_log_norm_zero_factor, intervalIntegral.integral_const, integral_re_mul_horizontal]
  simp only [smul_eq_mul]
  ring

theorem xiGenusLog_shift_eq_zero_ratio (p : RiemannXiDivisorZeroIndex) (T a b : ℝ) :
    (∫ x in a..b, xiGenusLog (horizontalAt T x) p) -
      (∫ x in (a + 1)..(b + 1), xiGenusLog (horizontalAt T x) p) =
      (∫ x in a..b, Real.log ‖(horizontalAt T x - riemannXiDivisorZeroValue p) /
        (horizontalAt T (x + 1) - riemannXiDivisorZeroValue p)‖) -
          (b - a) * ((riemannXiDivisorZeroValue p)⁻¹).re := by
  rw [xiGenusLog_integral_eq_kernel, xiGenusLog_integral_eq_kernel,
    integral_log_norm_zero_ratio]
  ring

theorem xi_zero_ratio_integral_summable {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (∫ x in a..b, Real.log ‖(horizontalAt T x - riemannXiDivisorZeroValue p) /
        (horizontalAt T (x + 1) - riemannXiDivisorZeroValue p)‖) -
          (b - a) * ((riemannXiDivisorZeroValue p)⁻¹).re) := by
  simpa only [xiGenusLog_shift_eq_zero_ratio] using
    (xiGenusLog_integral_summable hab T).sub
      (xiGenusLog_integral_summable (by linarith : a + 1 ≤ b + 1) T)

theorem xi_lehman_unit_shift_series (T : ℝ) :
    (∫ x in (1 / 2 : ℝ)..(3 / 2),
      Real.log ‖riemannXi (horizontalAt T x) /
        riemannXi (horizontalAt T (x + 1))‖) =
      -(logDeriv riemannXi 0).re +
        ∑' p : RiemannXiDivisorZeroIndex,
          ((∫ x in (1 / 2 : ℝ)..(3 / 2),
            Real.log ‖(horizontalAt T x - riemannXiDivisorZeroValue p) /
              (horizontalAt T (x + 1) - riemannXiDivisorZeroValue p)‖) -
            ((riemannXiDivisorZeroValue p)⁻¹).re) := by
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc (1 / 2 : ℝ) (3 / 2) →
      Real.log ‖riemannXi (horizontalAt T x) / riemannXi (horizontalAt T (x + 1))‖ =
        Real.log ‖riemannXi (horizontalAt T x)‖ -
          Real.log ‖riemannXi (horizontalAt T (x + 1))‖ := by
    filter_upwards [xi_horizontal_ne_zero_ae T] with x hx hxI
    have hd : riemannXi (horizontalAt T (x + 1)) ≠ 0 := by
      intro hz
      have ht := (xi_zero_strip hz).2
      have hx' := (Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) ▸ hxI).1
      simp only [horizontalAt, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im] at ht
      linarith
    rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hd)]
  have hi : IntervalIntegrable
      (fun x => Real.log ‖riemannXi (horizontalAt T (x + 1))‖) volume (1 / 2) (3 / 2) := by
    have h := (xi_horizontal_log_integrable T (3 / 2) (5 / 2)).comp_add_right 1
    norm_num at h
    exact h
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_sub (xi_horizontal_log_integrable T _ _) hi,
    intervalIntegral.integral_comp_add_right
      (fun x => Real.log ‖riemannXi (horizontalAt T x)‖) 1,
    xi_horizontal_unit_shift_integral (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) T]
  simp_rw [xiGenusLog_shift_eq_zero_ratio]
  norm_num

#print axioms xiGenusLog_eq_zero_log
#print axioms xiGenusLog_integral_eq_kernel
#print axioms xi_zero_ratio_integral_summable
#print axioms xi_lehman_unit_shift_series

end LiuWang.Proof.Campaign20260915.ZetaWinding
