import LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.GeometryBounds

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem denominator_upper_strip {z : ℂ} (hz : 1 / 32 ≤ z.im) :
    1 / 8 ≤ ‖rsHankelDenominator z‖ := by
  have hx : 1 / 7 ≤ 2 * Real.pi * z.im := by
    nlinarith [Real.pi_gt_three]
  have he : 8 / 7 ≤ Real.exp (2 * Real.pi * z.im) := by
    linarith [Real.add_one_le_exp (2 * Real.pi * z.im)]
  have he' : Real.exp (-(2 * Real.pi * z.im)) ≤ 7 / 8 := by
    rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith
  have hn : ‖exp (2 * Real.pi * I * z)‖ = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [norm_exp]
    congr 1
    simp
  have h := norm_sub_norm_le (1 : ℂ) (exp (2 * Real.pi * I * z))
  rw [norm_one, hn, norm_sub_rev] at h
  exact (by linarith : 1 / 8 ≤ 1 - Real.exp (-(2 * Real.pi * z.im))).trans h

theorem denominator_lower_strip {z : ℂ} (hz : z.im ≤ -(1 / 32)) :
    1 / 8 ≤ ‖rsHankelDenominator z‖ := by
  have hx : 1 / 8 ≤ -(2 * Real.pi * z.im) := by
    nlinarith [Real.pi_gt_three]
  have hn : ‖exp (2 * Real.pi * I * z)‖ = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [norm_exp]
    congr 1
    simp
  have h := norm_sub_norm_le (exp (2 * Real.pi * I * z)) (1 : ℂ)
  rw [norm_one, hn] at h
  exact (by linarith [Real.add_one_le_exp (-(2 * Real.pi * z.im))] :
    1 / 8 ≤ Real.exp (-(2 * Real.pi * z.im)) - 1).trans h

theorem denominator_half_integer_window {z : ℂ} {m : ℕ}
    (hz : |z.re + ((m : ℝ) + 1 / 2)| ≤ 1 / 4) :
    1 ≤ ‖rsHankelDenominator z‖ := by
  have hcos : Real.cos (2 * Real.pi * z.re) ≤ 0 := by
    have hx : 2 * Real.pi * z.re =
        (2 * Real.pi * (z.re + ((m : ℝ) + 1 / 2)) - m * (2 * Real.pi)) -
          Real.pi := by ring
    rw [hx, Real.cos_sub_pi, Real.cos_sub_nat_mul_two_pi]
    apply neg_nonpos.mpr
    apply Real.cos_nonneg_of_mem_Icc
    obtain ⟨hl, hu⟩ := abs_le.mp hz
    constructor <;> nlinarith [Real.pi_pos]
  have hR : (rsHankelDenominator z).re ≤ -1 := by
    have hx : (2 * Real.pi * I * z).im = 2 * Real.pi * z.re := by simp
    simp only [rsHankelDenominator, sub_re, exp_re, one_re, hx]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_pos (2 * Real.pi * I * z).re).le hcos]
  have h := (abs_le.mp (abs_re_le_norm (rsHankelDenominator z))).1
  linarith

theorem left_denominator_bound {eta : ℝ} {m : ℕ}
    (he : 1 ≤ eta) (hm : (m : ℝ) ≤ eta) (r : ℝ) :
    1 / 8 ≤ ‖rsHankelDenominator (rsC2LeftPoint eta m r)‖ := by
  by_cases hu : 1 / 32 ≤ (rsC2LeftPoint eta m r).im
  · exact denominator_upper_strip hu
  by_cases hl : (rsC2LeftPoint eta m r).im ≤ -(1 / 32)
  · exact denominator_lower_strip hl
  have hw := left_axis_window he hm (r := r) (abs_le.mpr ⟨by linarith, by linarith⟩)
  exact (by norm_num : (1 / 8 : ℝ) ≤ 1).trans (denominator_half_integer_window hw)

end LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
