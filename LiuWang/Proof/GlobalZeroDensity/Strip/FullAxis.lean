import LiuWang.Proof.GlobalZeroDensity.Strip.WeightedRight

/-! Actual full-axis square integrability throughout the closed moving strip. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity.Sharp
open Complex.HadamardThreeLines

namespace LiuWang.Proof.GlobalZeroDensity.Strip

theorem polynomial_exponential_abs_integrable {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    Integrable (fun t : ℝ => (a + b * |t|) ^ 2 * Real.exp (-|t| / r)) := by
  apply integrable_abs_of_integrableOn
    (v := fun t : ℝ => (a + b * t) ^ 2 * Real.exp (-t / r))
  have h0 := (exp_moment_integrable hr 0).const_mul (a ^ 2)
  have h1 := (exp_moment_integrable hr 1).const_mul (2 * a * b)
  have h2 := (exp_moment_integrable hr 2).const_mul (b ^ 2)
  have heq : (fun t : ℝ => (a + b * t) ^ 2 * Real.exp (-t / r)) =
      (fun t : ℝ => a ^ 2 * (t ^ 0 * Real.exp (-t / r)) +
        2 * a * b * (t ^ 1 * Real.exp (-t / r)) +
        b ^ 2 * (t ^ 2 * Real.exp (-t / r))) := by ext t; ring
  rw [heq]
  exact (h0.fun_add h1).fun_add h2

theorem regularG_strip_integrable {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) :
    Integrable (fun t : ℝ => ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
  have hd := delta_bounds hy
  have hc := continuous_vertical_regularG (by linarith : 0 < y)
    (by linarith [hσ.1] : 0 < σ)
    (by nlinarith [hσ.2, Real.pi_gt_three] : σ < Real.pi * y)
  obtain ⟨B, hB⟩ := regularG_bounded hy
  have hb (t : ℝ) : ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ≤ max B 0 := by
    apply le_trans _ (le_max_left B 0)
    apply hB
    exact mem_image_of_mem _ (by simpa [verticalClosedStrip] using hσ)
  let a : ℝ := 8 * (⌈y⌉₊ : ℝ) + 1
  let b : ℝ := 2 * (⌈y⌉₊ : ℝ)
  let v : ℝ → ℝ := (Icc (-1 : ℝ) 1).indicator (fun _ => (max B 0) ^ 2)
  have hv : Integrable v := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    exact integrableOn_const (hs := isCompact_Icc.measure_ne_top)
  have hp := (polynomial_exponential_abs_integrable
    (by positivity : 0 < (4 / 3) * y) a b).const_mul (21 / 10 : ℝ)
  apply (hv.fun_add hp).mono' (hc.norm.fun_pow 2).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have ht0 : 0 ≤ (21 / 10 : ℝ) * ((a + b * |t|) ^ 2 *
      Real.exp (-|t| / ((4 / 3) * y))) := by positivity
  by_cases ht : |t| ≤ 1
  · have hv' : v t = (max B 0) ^ 2 := by
      exact indicator_of_mem (show t ∈ Icc (-1 : ℝ) 1 from abs_le.mp ht) _
    rw [hv']
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hb t) 2
    linarith
  · have ht1 : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    let s := (σ : ℂ) + t * Complex.I
    have hs1 : s ≠ 1 := by
      intro h
      have hh := congrArg Complex.im h
      simp [s] at hh
      simp [hh] at ht1
      norm_num at ht1
    have hz := norm_riemannZeta_lt_linear_im_on_strip s
      ⟨by simpa [s] using hσ.1, by dsimp [s]; simp; linarith [hσ.2]⟩
      (by simpa [s] using ht1)
    have hq := norm_Q_strip_le (s := s) (by simp [s]; linarith [hσ.1]) y
    have hf := norm_sub_le (riemannZeta s * Q y s) 1
    rw [norm_mul, norm_one] at hf
    have hm := mul_le_mul hz.le hq (norm_nonneg _) (by positivity)
    have hnf : ‖f y s‖ ≤ a + b * |t| := by
      dsimp [a, b, f, s] at *
      simp only [Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at *
      nlinarith
    have hF : F y s ≤ (a + b * |t|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnf 2
    have hg := regularG_weight hy hs1 (by simpa [s] using hσ.1)
      (by simp [s]; linarith [hσ.2])
    have hmF := mul_le_mul_of_nonneg_right hF
      (Real.exp_pos (-|t| / ((4 / 3) * y))).le
    have hv0 : 0 ≤ v t := indicator_nonneg (fun _ _ => sq_nonneg _) t
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hg
    dsimp [s] at hmF
    nlinarith

end LiuWang.Proof.GlobalZeroDensity.Strip
