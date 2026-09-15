import LiuWang.Proof.GlobalZeroDensity.Strip.WeightedCritical

/-! A proved full-line right mean; its explicit y-factor is not the source log-only bound. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.GlobalZeroDensity.Strip

theorem exponential_abs_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (fun t : ℝ => Real.exp (-|t| / r)) := by
  apply integrable_abs_of_integrableOn (v := fun t : ℝ => Real.exp (-t / r))
  simpa only [pow_zero, one_mul] using exp_moment_integrable hr 0

theorem exponential_abs_integral {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ, Real.exp (-|t| / r)) = 2 * r := by
  rw [integral_comp_abs (f := fun t : ℝ => Real.exp (-t / r))]
  have h := exp_moment_integral hr 0
  simp only [pow_zero, one_mul, zero_add, pow_one, Nat.factorial_zero, Nat.cast_one, mul_one] at h
  rw [h]

theorem regularG_right_envelope {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : 1 + delta y ≤ σ) (hσ4 : σ ≤ 4) (t : ℝ) :
    ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (3549 / 1000) * Real.log y ^ 4 * Real.exp (-|t| / ((4 / 3) * y)) := by
  have hd := delta_bounds hy
  have hs1 : (σ : ℂ) + t * Complex.I ≠ 1 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hg := regularG_weight hy hs1 (by simpa using (show 1 / 2 ≤ σ by linarith))
    (by simpa using hσ4)
  have hf := F_right_half hy (s := (σ : ℂ) + t * Complex.I) (by simpa using hσ)
  have hm := mul_le_mul_of_nonneg_right hf (Real.exp_pos (-|t| / ((4 / 3) * y))).le
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hg
  nlinarith

theorem regularG_right_integrable {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : 1 + delta y ≤ σ) (hσ4 : σ ≤ 4) :
    Integrable (fun t : ℝ => ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
  have hd := delta_bounds hy
  have hc := continuous_vertical_regularG (by linarith : 0 < y)
    (by linarith : 0 < σ) (by nlinarith [Real.pi_gt_three] : σ < Real.pi * y)
  apply ((exponential_abs_integrable (by positivity : 0 < (4 / 3) * y)).const_mul
    ((3549 / 1000) * Real.log y ^ 4)).mono' (hc.norm.fun_pow 2).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact regularG_right_envelope hy hσ hσ4 t

theorem weightedMean_right_bound {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : 1 + delta y ≤ σ) (hσ4 : σ ≤ 4) :
    weightedMean y σ ≤ (1183 / 125) * y * Real.log y ^ 4 := by
  have h := integral_mono (regularG_right_integrable hy hσ hσ4)
    ((exponential_abs_integrable (by positivity : 0 < (4 / 3) * y)).const_mul
      ((3549 / 1000) * Real.log y ^ 4))
    (regularG_right_envelope hy hσ hσ4)
  rw [integral_const_mul, exponential_abs_integral (by positivity : 0 < (4 / 3) * y)] at h
  change (∫ t : ℝ, ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤ _
  convert h using 1
  · rfl
  · ring

end LiuWang.Proof.GlobalZeroDensity.Strip
