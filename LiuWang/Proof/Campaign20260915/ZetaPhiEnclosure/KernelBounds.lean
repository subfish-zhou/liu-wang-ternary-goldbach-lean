import LiuWang.Proof.Campaign20260915.ZetaMordell.CorrectionPolynomials
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem siegel_denominator_im (t : ℝ) :
    (exp (Real.pi * I * siegelLine t) - exp (-Real.pi * I * siegelLine t)).im =
      (Real.exp (-Real.pi * t) + Real.exp (Real.pi * t)) * Real.cos (Real.pi * t) := by
  have hp : (Real.pi * I * siegelLine t).im = Real.pi / 2 - Real.pi * t := by
    simp [siegelLine, mul_re, mul_im]
    ring
  have hm : (-Real.pi * I * siegelLine t).im = -(Real.pi / 2 - Real.pi * t) := by
    simp [siegelLine, mul_re, mul_im]
    ring
  simp only [sub_im, Complex.exp_im, hp, hm, Real.sin_neg, Real.sin_pi_div_two_sub]
  have hr : (Real.pi * I * siegelLine t).re = -Real.pi * t := by
    simp [siegelLine, mul_re, mul_im]
  have hs : (-Real.pi * I * siegelLine t).re = Real.pi * t := by
    simp [siegelLine, mul_re, mul_im]
  rw [hr, hs]
  ring

theorem siegel_denominator_lower (t : ℝ) :
    Real.exp (Real.pi * |t|) / 2 ≤
      ‖exp (Real.pi * I * siegelLine t) - exp (-Real.pi * I * siegelLine t)‖ := by
  have hnorm : ‖exp (Real.pi * I * siegelLine t)‖ = Real.exp (-Real.pi * t) := by
    rw [norm_exp]
    congr 1
    simp [siegelLine, mul_re, mul_im]
  have hnorm' : ‖exp (-Real.pi * I * siegelLine t)‖ = Real.exp (Real.pi * t) := by
    rw [norm_exp]
    congr 1
    simp [siegelLine, mul_re, mul_im]
  by_cases ht : |t| ≤ 1 / 4
  · have hx : |Real.pi * t| ≤ 1 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_lt_four, abs_nonneg t]
    have hc : 1 / 2 ≤ Real.cos (Real.pi * t) := by
      have hs := (sq_le_one_iff_abs_le_one (Real.pi * t)).mpr hx
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := Real.pi * t)]
    have he : Real.exp (Real.pi * |t|) ≤
        Real.exp (-Real.pi * t) + Real.exp (Real.pi * t) := by
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h]
        linarith [Real.exp_pos (-Real.pi * t)]
      · rw [abs_of_nonpos h, mul_neg, ← neg_mul]
        linarith [Real.exp_pos (Real.pi * t)]
    have hi := im_le_norm
      (exp (Real.pi * I * siegelLine t) - exp (-Real.pi * I * siegelLine t))
    rw [siegel_denominator_im] at hi
    nlinarith [mul_le_mul_of_nonneg_left hc
      (show 0 ≤ Real.exp (-Real.pi * t) + Real.exp (Real.pi * t) by positivity)]
  · have ha : 1 / 2 ≤ Real.pi * |t| := by
      nlinarith [Real.two_le_pi, abs_nonneg t]
    have he : 2 ≤ Real.exp (2 * (Real.pi * |t|)) :=
      (by linarith : 2 ≤ 2 * (Real.pi * |t|) + 1).trans (Real.add_one_le_exp _)
    have hp := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(Real.pi * |t|))).le
    rw [← Real.exp_add, show 2 * (Real.pi * |t|) + -(Real.pi * |t|) =
      Real.pi * |t| by ring] at hp
    have hd : Real.exp (Real.pi * |t|) - Real.exp (-(Real.pi * |t|)) ≤
        ‖exp (Real.pi * I * siegelLine t) - exp (-Real.pi * I * siegelLine t)‖ := by
      rcases le_total 0 t with h | h
      · have hh := norm_sub_norm_le (exp (-Real.pi * I * siegelLine t))
          (exp (Real.pi * I * siegelLine t))
        rw [hnorm, hnorm', norm_sub_rev] at hh
        simpa only [abs_of_nonneg h, neg_mul] using hh
      · have hh := norm_sub_norm_le (exp (Real.pi * I * siegelLine t))
          (exp (-Real.pi * I * siegelLine t))
        rw [hnorm, hnorm'] at hh
        simpa only [abs_of_nonpos h, mul_neg, neg_neg, neg_mul] using hh
    linarith

theorem correctionKernel_real_bound {z : ℝ} (hz : |z| ≤ 1) (t : ℝ) :
    ‖correctionKernel z t‖ ≤ 4 * Real.exp (-2 * Real.pi * t ^ 2 + Real.pi * |t|) := by
  have hf : ‖correctionFactor (z : ℂ)‖ = 1 := by
    rw [correctionFactor, norm_exp]
    simp [mul_re, mul_im, pow_two]
  have hn :
      ‖exp (-Real.pi * I * siegelLine t ^ 2 +
        2 * Real.pi * I * ((z : ℂ) + 1 / 2) * siegelLine t)‖ =
      Real.exp (-2 * Real.pi * t ^ 2 - 2 * Real.pi * z * t) := by
    rw [norm_exp]
    congr 1
    simp [siegelLine, pow_two, mul_re, mul_im]
    ring
  have hr : ‖(-1 : ℂ) + I‖ ≤ 2 := by
    simpa only [norm_neg, norm_one, norm_I, one_add_one_eq_two] using norm_add_le (-1 : ℂ) I
  have hd := siegel_denominator_lower t
  have hdpos := lt_of_lt_of_le (by positivity : 0 < Real.exp (Real.pi * |t|) / 2) hd
  rw [correctionKernel_normalization, norm_mul, hf, one_mul, siegelKernel,
    norm_mul, norm_div, hn]
  apply (mul_le_mul_of_nonneg_left hr (by positivity)).trans
  rw [div_mul_eq_mul_div, div_le_iff₀ hdpos]
  have hzt : -z * t ≤ |t| := by
    calc
      -z * t ≤ |(-z) * t| := le_abs_self _
      _ = |z| * |t| := by rw [abs_mul, abs_neg]
      _ ≤ |t| := by nlinarith [mul_le_mul_of_nonneg_right hz (abs_nonneg t)]
  have he : Real.exp (-2 * Real.pi * t ^ 2 - 2 * Real.pi * z * t) ≤
      Real.exp (-2 * Real.pi * t ^ 2 + Real.pi * |t|) * Real.exp (Real.pi * |t|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  nlinarith [mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 4 * Real.exp (-2 * Real.pi * t ^ 2 + Real.pi * |t|) by positivity)]

theorem correction_center_norm {z : ℝ} (hz : |z| ≤ 1) (t : ℝ) :
    ‖siegelLine t - ((z : ℂ) + 1) / 2‖ ≤ 1 / 2 + 2 * |t| := by
  have he : siegelLine t - ((z : ℂ) + 1) / 2 =
      -(z : ℂ) / 2 + (-1 + I) * t := by
    unfold siegelLine
    ring
  have hr : ‖(-1 : ℂ) + I‖ ≤ 2 := by
    simpa only [norm_neg, norm_one, norm_I, one_add_one_eq_two] using norm_add_le (-1 : ℂ) I
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_div, norm_neg, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_right hr (abs_nonneg t)]

theorem correction_moment_kernel_bound (n : ℕ) {z : ℝ} (hz : |z| ≤ 1) (t : ℝ) :
    ‖(siegelLine t - ((z : ℂ) + 1) / 2) ^ n * correctionKernel z t‖ ≤
      (108 * (n.factorial : ℝ)) * Real.exp (-Real.pi * t ^ 2) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hp : ‖siegelLine t - ((z : ℂ) + 1) / 2‖ ^ n ≤
      (n.factorial : ℝ) * Real.exp (1 / 2 + 2 * |t|) := by
    have h := (div_le_iff₀ hf).mp
      (Real.pow_div_factorial_le_exp (1 / 2 + 2 * |t|) (by positivity) n)
    exact (pow_le_pow_left₀ (norm_nonneg _) (correction_center_norm hz t) n).trans
      (by nlinarith)
  have hphase : 1 / 2 + 2 * |t| + (-2 * Real.pi * t ^ 2 + Real.pi * |t|) ≤
      3 + (-Real.pi * t ^ 2) := by
    have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
    have h1 := mul_nonneg (show 0 ≤ Real.pi - 3 by linarith)
      (sq_nonneg (|t| - 1 / 2))
    nlinarith [sq_nonneg (|t| - 5 / 6), sq_abs t, Real.pi_lt_four]
  have he : Real.exp (3 : ℝ) ≤ 27 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
    norm_num [← Real.exp_nat_mul] at h ⊢
    exact h
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ((n.factorial : ℝ) * Real.exp (1 / 2 + 2 * |t|)) *
        (4 * Real.exp (-2 * Real.pi * t ^ 2 + Real.pi * |t|)) :=
      mul_le_mul hp (correctionKernel_real_bound hz t) (norm_nonneg _) (by positivity)
    _ = 4 * (n.factorial : ℝ) *
        Real.exp (1 / 2 + 2 * |t| + (-2 * Real.pi * t ^ 2 + Real.pi * |t|)) := by
      simp only [Real.exp_add]
      ring
    _ ≤ 4 * (n.factorial : ℝ) * Real.exp (3 + (-Real.pi * t ^ 2)) := by
      gcongr
    _ ≤ _ := by
      rw [Real.exp_add]
      nlinarith [mul_le_mul_of_nonneg_right he
        (show 0 ≤ 4 * (n.factorial : ℝ) * Real.exp (-Real.pi * t ^ 2) by positivity)]

theorem correctionMoment_bound (n : ℕ) {z : ℝ} (hz : |z| ≤ 1) :
    ‖correctionMoment n z‖ ≤ 108 * (n.factorial : ℝ) := by
  calc
    _ ≤ ∫ t : ℝ, (108 * (n.factorial : ℝ)) * Real.exp (-Real.pi * t ^ 2) := by
      apply norm_integral_le_of_norm_le
        ((integrable_exp_neg_mul_sq Real.pi_pos).const_mul _)
      exact Filter.Eventually.of_forall (correction_moment_kernel_bound n hz)
    _ = _ := by
      rw [integral_const_mul, integral_gaussian]
      simp [Real.pi_ne_zero]

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
