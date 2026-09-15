import LiuWang.Proof.GlobalZeroDensity.Sharp.MeanBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Feeding the oscillatory mollifier mean into the actual detector integral. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem norm_zeta_sq_height (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ 8 * (2 + |t|) := by
  by_cases ht : ‖(1 / 2 : ℂ) + t * Complex.I‖ ≤ 2
  · have h := pow_le_pow_left₀ (norm_nonneg _) (norm_zeta_small_norm ht) 2
    nlinarith [abs_nonneg t]
  · have h := pow_le_pow_left₀ (norm_nonneg _)
      (norm_zeta_large_norm (le_of_not_ge ht)) 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at h
    have hr := (critical_norm_bounds t).2
    nlinarith [abs_nonneg t]

theorem F_le_mollifier_sq (y t : ℝ) :
    F y ((1 / 2 : ℂ) + t * Complex.I) ≤
      (202 / 25) * (2 + |t|) * ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 + 101 := by
  let z := riemannZeta ((1 / 2 : ℂ) + t * Complex.I)
  let q := Q y ((1 / 2 : ℂ) + t * Complex.I)
  have hn := norm_sub_le (z * q) 1
  rw [norm_mul, norm_one] at hn
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hζ := mul_le_mul_of_nonneg_right (norm_zeta_sq_height t) (sq_nonneg ‖q‖)
  have hY := sq_nonneg (‖z‖ * ‖q‖ - 100)
  change ‖z * q - 1‖ ^ 2 ≤ _
  change ‖z‖ ^ 2 * ‖q‖ ^ 2 ≤ _ at hζ
  change ‖z * q - 1‖ ^ 2 ≤ (202 / 25) * (2 + |t|) * ‖q‖ ^ 2 + 101
  nlinarith

theorem M_critical_le_Q_mean (y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    M y (1 / 2) u ≤
      (202 / 25) * (2 + u) *
        (∫ t in -u..u, ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) +
      202 * u := by
  have hpoint : ∀ t ∈ Set.Icc (-u) u,
      F y (((1 / 2 : ℝ) : ℂ) + t * Complex.I) ≤
        (202 / 25) * (2 + u) * ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 + 101 := by
    intro t ht
    have habs : |t| ≤ u := abs_le.mpr ht
    have h := F_le_mollifier_sq y t
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    nlinarith [mul_nonneg (sub_nonneg.mpr habs)
      (sq_nonneg ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖)]
  have hi := Q_mean_integrable y u
  have hj := intervalIntegrable_F y u (σ := 1 / 2) (by norm_num)
  have hk := (hi.const_mul ((202 / 25) * (2 + u))).add
    (intervalIntegrable_const (c := (101 : ℝ)))
  have h := intervalIntegral.integral_mono_on (by linarith : -u ≤ u) hj hk hpoint
  rw [intervalIntegral.integral_add (hi.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h
  simp only [M]
  simp only [smul_eq_mul] at h
  linarith

theorem M_critical_from_mean (y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    M y (1 / 2) u ≤
      (202 / 25) * (2 + u) *
        ((2 * u + 4 * (⌈y⌉₊ : ℝ)) * (1 + Real.log ⌈y⌉₊) + 4 * (⌈y⌉₊ : ℝ)) +
      202 * u := by
  have h := M_critical_le_Q_mean y hu
  have hm := mul_le_mul_of_nonneg_left (Q_mean_le y hu)
    (show 0 ≤ (202 / 25) * (2 + u) by positivity)
  linarith

theorem log_ge_nine {y : ℝ} (hy : 10000 ≤ y) : 9 ≤ Real.log y := by
  have hexp : Real.exp 1 ≤ 11 / 4 := le_of_lt
    (Real.exp_one_lt_d9.trans (by norm_num))
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le hexp 9
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have he : Real.exp 9 ≤ y := by linarith
  exact (Real.le_log_iff_exp_le (by linarith)).mpr he

theorem ceil_log_bounds {y : ℝ} (hy : 10000 ≤ y) :
    (⌈y⌉₊ : ℝ) ≤ (1001 / 1000) * y ∧
      Real.log ⌈y⌉₊ ≤ Real.log y + 1 / 1000 := by
  have hy0 : 0 < y := by linarith
  have hc : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
  have hn : (⌈y⌉₊ : ℝ) ≤ (1001 / 1000) * y := by linarith
  have hn0 : (0 : ℝ) < ⌈y⌉₊ := hy0.trans_le (Nat.le_ceil y)
  have hl := Real.log_le_sub_one_of_pos (div_pos hn0 hy0)
  rw [Real.log_div (ne_of_gt hn0) (ne_of_gt hy0)] at hl
  have hd : (⌈y⌉₊ : ℝ) / y ≤ 1001 / 1000 := (div_le_iff₀ hy0).mpr hn
  exact ⟨hn, by linarith⟩

theorem Q_mean_at_height_bound {y : ℝ} (hy : 10000 ≤ y) :
    (2 * y + 4 * (⌈y⌉₊ : ℝ)) * (1 + Real.log ⌈y⌉₊) + 4 * (⌈y⌉₊ : ℝ) ≤
      (36 / 5) * y * Real.log y := by
  have hlog := log_ge_nine hy
  obtain ⟨hN, hlogN⟩ := ceil_log_bounds hy
  have hp := mul_le_mul
    (show 2 * y + 4 * (⌈y⌉₊ : ℝ) ≤ (1501 / 250) * y by linarith)
    (show 1 + Real.log ⌈y⌉₊ ≤ Real.log y + 1001 / 1000 by linarith)
    (show 0 ≤ 1 + Real.log ⌈y⌉₊ by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ ⌈y⌉₊ by
        have := Nat.le_ceil y; linarith)
      linarith)
    (show 0 ≤ (1501 / 250) * y by positivity)
  have hyl := mul_le_mul_of_nonneg_left hlog (show 0 ≤ y by linarith)
  nlinarith

theorem M_critical_at_height {y : ℝ} (hy : 10000 ≤ y) :
    M y (1 / 2) y ≤ 60 * y ^ 2 * Real.log y := by
  have hy0 : 0 ≤ y := by linarith
  have hlog := log_ge_nine hy
  have hb := Q_mean_at_height_bound hy
  have h := M_critical_from_mean y hy0
  have hp := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (202 / 25) * (2 + y) by positivity)
  have hscale : (202 / 25) * (2 + y) ≤ (81 / 10) * y := by linarith
  have hmain := mul_le_mul_of_nonneg_right hscale
    (show 0 ≤ (36 / 5) * y * Real.log y by positivity)
  have herror : 202 * y ≤ y ^ 2 * Real.log y := by
    have h1 : 202 ≤ y * Real.log y := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hy0
    nlinarith
  nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ Real.log y by linarith)]

end LiuWang.Proof.GlobalZeroDensity.Sharp
