import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.MeanBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Removing the genuine g-weight, with an integrated low-height pole factor. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip
open Complex.HadamardThreeLines

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem height_cos_bound {y t : ℝ} (hy : 10000 ≤ y) (ht : |t| ≤ y) (σ : ℝ) :
    ‖Complex.cos (((σ : ℂ) + t * I) / (2 * (y : ℂ)))‖ ^ 2 ≤ 13 / 10 := by
  have hi : (((σ : ℂ) + t * I) / (2 * (y : ℂ))).im = t / (2 * y) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
    simp
  have hc := norm_cos_le_cosh (((σ : ℂ) + t * I) / (2 * (y : ℂ)))
  rw [hi] at hc
  have hhalf : Real.cosh (t / (2 * y)) ≤ Real.cosh (1 / 2) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * y)]
    norm_num
    exact (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr (by linarith)
  have hb := cosh_near_half (x := 1 / 2) (by norm_num) (by norm_num)
  have hp := pow_le_pow_left₀ (norm_nonneg _) (hc.trans (hhalf.trans hb)) 2
  norm_num at hp
  linarith

theorem F_unweight {y σ t : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 - delta y)) :
    F y ((σ : ℂ) + t * I) =
      ((σ ^ 2 + t ^ 2) / ((1 - σ) ^ 2 + t ^ 2)) *
        ‖Complex.cos (((σ : ℂ) + t * I) / (2 * (y : ℂ)))‖ ^ 2 *
        ‖regularG y ((σ : ℂ) + t * I)‖ ^ 2 := by
  let s := (σ : ℂ) + t * I
  have hd := delta_bounds hy
  have hs1 : s ≠ 1 := by
    intro h; have hh := congrArg Complex.re h; simp [s] at hh; linarith [hσ.2]
  have hs : s ∈ verticalClosedStrip (1 / 2) (1 + delta y) := by
    change 1 / 2 ≤ s.re ∧ s.re ≤ 1 + delta y
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, zero_mul, sub_self, add_zero]
    constructor <;> linarith [hσ.1, hσ.2]
  have hden := strip_denominator_ne_zero (by linarith : 0 < y) (closed_strip_safe hy hs)
  have hsf : ‖f y s‖ ^ 2 =
      (‖s‖ ^ 2 / ‖s - 1‖ ^ 2) * ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2 *
        ‖regularG y s‖ ^ 2 := by
    rw [regularG_eq_g hs1, g, norm_mul, norm_div, norm_mul, mul_pow, div_pow, mul_pow]
    have hs0 : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr (left_ne_zero_of_mul hden)
    have hc0 : ‖Complex.cos (s / (2 * (y : ℂ)))‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (right_ne_zero_of_mul hden)
    have h10 : ‖s - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1)
    field_simp
  have hs2 : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    simp [s, Complex.sq_norm, Complex.normSq_apply]; ring
  have h12 : ‖s - 1‖ ^ 2 = (1 - σ) ^ 2 + t ^ 2 := by
    simp [s, Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hs2, h12] at hsf
  exact hsf

theorem F_high_unweight {y σ t : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 - delta y)) (ht0 : 1 ≤ |t|) (ht : |t| ≤ y) :
    F y ((σ : ℂ) + t * I) ≤ (13 / 5) * ‖regularG y ((σ : ℂ) + t * I)‖ ^ 2 := by
  have hd := delta_bounds hy
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have hr : (σ ^ 2 + t ^ 2) / ((1 - σ) ^ 2 + t ^ 2) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (1 - σ) ^ 2 + t ^ 2)).mpr
    nlinarith [hσ.1, hσ.2, sq_nonneg (1 - σ)]
  have hm := mul_le_mul hr (height_cos_bound hy ht σ) (sq_nonneg _) (by norm_num)
  rw [F_unweight hy hσ]
  have h := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖regularG y ((σ : ℂ) + t * I)‖)
  nlinarith

theorem F_low_unweight {y σ t : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 - delta y)) (ht : |t| ≤ 1) :
    F y ((σ : ℂ) + t * I) ≤
      43 * (y ^ (4 * (1 - σ)) * Real.log y ^ (8 * σ - 4)) *
        (1 + ((1 - σ) ^ 2 + t ^ 2)⁻¹) := by
  have hd := delta_bounds hy
  have hL := log_ge_nine hy
  have hσ1 : σ < 1 := by linarith [hσ.2]
  have hden : 0 < (1 - σ) ^ 2 + t ^ 2 := by have := sq_pos_of_pos (sub_pos.mpr hσ1); positivity
  have hr : (σ ^ 2 + t ^ 2) / ((1 - σ) ^ 2 + t ^ 2) ≤
      1 + ((1 - σ) ^ 2 + t ^ 2)⁻¹ := by
    apply (div_le_iff₀ hden).mpr
    rw [add_mul, inv_mul_cancel₀ hden.ne']
    nlinarith [hσ.2]
  have hc := height_cos_bound hy (ht.trans (by linarith : 1 ≤ y)) σ
  have hg := regularG_strip_source hy (s := (σ : ℂ) + t * I)
    (by change 1 / 2 ≤ _ ∧ _ ≤ 1 + delta y; simp; constructor <;> linarith [hσ.1, hσ.2])
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, zero_mul, sub_self, add_zero] at hg
  rw [F_unweight hy hσ]
  have hm := mul_le_mul hr hc (sq_nonneg _) (by positivity)
  have hp := mul_le_mul hm hg (sq_nonneg _) (by positivity)
  have hpos : 0 ≤ (y ^ (4 * (1 - σ)) * Real.log y ^ (8 * σ - 4)) *
      (1 + ((1 - σ) ^ 2 + t ^ 2)⁻¹) := by positivity
  nlinarith

theorem low_pole_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in (-1 : ℝ)..1, 1 + (a ^ 2 + t ^ 2)⁻¹) ≤ 2 + Real.pi / a := by
  have hc : Continuous (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) :=
    (continuous_const.add (continuous_id.pow 2)).inv₀
      (fun t => ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)))
  rw [intervalIntegral.integral_add intervalIntegrable_const (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_inv_sq_add_sq ha.ne']
  simp only [sub_neg_eq_add, smul_eq_mul, mul_one]
  have hb : Real.arctan (1 / a) - Real.arctan (-1 / a) ≤ Real.pi := by
    linarith [Real.arctan_lt_pi_div_two (1 / a), Real.neg_pi_div_two_lt_arctan (-1 / a)]
  have h := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ha.le)
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem M_low_sharp {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 - delta y)) :
    M y σ 1 ≤ 301 * y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) := by
  have hd := delta_bounds hy
  have hL := log_ge_nine hy
  have hl0 : 0 < Real.log y := by linarith
  have hσ1 : σ < 1 := by linarith [hσ.2]
  have ha : 0 < 1 - σ := by linarith
  have hc : Continuous (fun t : ℝ => 1 + ((1 - σ) ^ 2 + t ^ 2)⁻¹) :=
    continuous_const.add ((continuous_const.add (continuous_id.pow 2)).inv₀
      (fun t => ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t))))
  let P := y ^ (4 * (1 - σ)) * Real.log y ^ (8 * σ - 4)
  have hmean := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (-1 : ℝ) ≤ 1)
    (intervalIntegrable_F y 1 hσ1.ne)
    ((hc.const_mul (43 * P)).intervalIntegrable _ _)
    (fun t ht => F_low_unweight hy hσ (abs_le.mpr ht))
  rw [intervalIntegral.integral_const_mul] at hmean
  have hlow := mul_le_mul_of_nonneg_left (low_pole_integral ha)
    (show 0 ≤ 43 * P by dsimp [P]; positivity)
  have hinv : 1 / (1 - σ) ≤ 3 * Real.log y / 2 := by
    have h := one_div_le_one_div_of_le hd.1 (by linarith [hσ.2] : delta y ≤ 1 - σ)
    have he : 1 / delta y = 3 * Real.log y / 2 := by unfold delta; field_simp
    exact h.trans_eq he
  have hpi : 2 + Real.pi / (1 - σ) ≤ 7 * Real.log y := by
    have h1 := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (by positivity : 0 ≤ 1 / (1 - σ))
    rw [mul_one_div, mul_one_div] at h1
    have h2 := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 4)
    rw [mul_one_div] at h2
    linarith
  have hp := mul_le_mul_of_nonneg_left hpi (show 0 ≤ 43 * P by dsimp [P]; positivity)
  have hpow : Real.log y ^ (8 * σ - 4) * Real.log y ≤ Real.log y ^ (6 * σ - 1) := by
    calc
      _ = Real.log y ^ (8 * σ - 4 + 1) := by rw [Real.rpow_add hl0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hpow' := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ 301 * y ^ (4 * (1 - σ)) by positivity)
  change (∫ t in (-1 : ℝ)..1, F y ((σ : ℂ) + t * I)) ≤ _
  dsimp [P] at *
  nlinarith

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
