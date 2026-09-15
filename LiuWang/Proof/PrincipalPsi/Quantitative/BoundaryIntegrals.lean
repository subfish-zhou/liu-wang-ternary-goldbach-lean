import LiuWang.Proof.PrincipalPsi.Quantitative.Rectangle
import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.SplitIntegral

/-! # 真实三条边的可积性与参数化积分界 -/

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open LiuWang.Proof.NonSymmetricContour
open LiuWang.Proof.LocalAnalyticBounds

namespace LiuWang.Proof.PrincipalPsi.Quantitative

theorem continuous_zeta_left {t : ℝ} (ht : 0 < t) :
    Continuous (fun u : ℝ => zetaCenteredIntegrand t ((-1 / 2 : ℂ) + u * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hs : ((-1 / 2 : ℂ) + u * I).re = -1 / 2 := by norm_num
  have hs1 : (-1 / 2 : ℂ) + u * I ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  exact (analytic_zetaCenteredIntegrand ht hs1 (zeta_ne_zero_left hs)).continuousAt.comp
    (f := fun u : ℝ => (-1 / 2 : ℂ) + u * I)
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt

theorem continuousOn_zeta_horizontal {t H B b : ℝ} (ht : 0 < t)
    (hB : 0 < B) (hH : H ≠ 0)
    (hsep : ∀ p : RiemannXiDivisorZeroIndex,
      B⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - H|) :
    ContinuousOn (fun σ : ℝ => zetaCenteredIntegrand t ((σ : ℂ) + H * I))
      (Set.Icc (-1 / 2) b) := by
  intro σ hσ
  have hs1 : (σ : ℂ) + H * I ≠ 1 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    exact hH hh
  have hz := zeta_ne_zero_separated hB hsep (s := (σ : ℂ) + H * I)
    (by simp) (by simpa using hσ.1)
  exact ((analytic_zetaCenteredIntegrand ht hs1 hz).continuousAt.comp
    (f := fun σ : ℝ => (σ : ℂ) + H * I)
    (Complex.continuous_ofReal.add continuous_const).continuousAt).continuousWithinAt

theorem norm_zeta_vertical_le {t U Hp Hm : ℝ} (ht : 9 ≤ t)
    (hm : |Hm| ≤ U) (hp : |Hp| ≤ U) :
    ‖verticalIntegral (zetaCenteredIntegrand t) (-1 / 2) Hp Hm‖ ≤
      60 * (U + 2) ^ 2 * |Hp - Hm| / (2 * Real.pi) := by
  have hU : 0 ≤ U := (abs_nonneg Hm).trans hm
  rw [norm_verticalIntegral]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro u hu
  have hum : u ∈ Set.uIcc Hm Hp := Set.uIoc_subset_uIcc hu
  have habs : |u| ≤ U := by
    rcases Set.mem_uIcc.mp hum with h | h
    · exact abs_le.mpr ⟨le_trans (abs_le.mp hm).1 h.1, le_trans h.2 (abs_le.mp hp).2⟩
    · exact abs_le.mpr ⟨le_trans (abs_le.mp hp).1 h.1, le_trans h.2 (abs_le.mp hm).2⟩
  have h := norm_zetaCenteredIntegrand_left ht
    (s := (-1 / 2 : ℂ) + u * I) (by norm_num)
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_im, Complex.I_re] at h
  norm_num at h
  simpa [neg_div] using h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by linarith : |u| + 2 ≤ U + 2) 2) (by norm_num))

theorem norm_zeta_horizontal_le {t H B b : ℝ}
    (ht : 1 < t) (hb : 1 ≤ b) (hb2 : b ≤ 2) (hB : 0 < B) (hH : 2 ≤ |H|)
    (hsep : ∀ p : RiemannXiDivisorZeroIndex,
      B⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - H|) :
    ‖horizontalIntegral (zetaCenteredIntegrand t) b H‖ ≤
      horizontalLogBound H B / |H| *
        (t ^ b / Real.log t + 7 * (b + 1 / 2)) / (2 * Real.pi) := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < Real.log t := Real.log_pos ht
  have hH0 : 0 < |H| := by linarith
  have hD : 0 ≤ horizontalLogBound H B := by
    unfold horizontalLogBound
    have hlog := Real.log_nonneg (show 1 ≤ |H| + 2 by linarith [abs_nonneg H])
    have hM := referenceMass_nonneg H
    positivity
  have hbound : ∀ σ ∈ Set.Ioc (-1 / 2 : ℝ) b,
      ‖zetaCenteredIntegrand t ((σ : ℂ) + H * I)‖ ≤
        horizontalLogBound H B / |H| * (t ^ σ + 7) := by
    intro σ hσ
    have hs0 : (σ : ℂ) + H * I ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      simp at hh
      norm_num [hh] at hH
    have hlog := norm_logDeriv_zeta_separated hB hH hsep
      (s := (σ : ℂ) + H * I) (by simp) (by simpa using hσ.1.le) (by simp; linarith [hσ.2])
    have h := HorizontalEstimate.norm_horizontalIntegrand_le_power
      (1 : DirichletCharacter ℂ 1) ht0 (s := (σ : ℂ) + H * I)
      (by simp; linarith [hσ.2]) (by simpa using hH0)
      (by simpa only [DirichletCharacter.LFunction_modOne_eq] using hlog)
    rw [zetaCenteredIntegrand_eq hs0]
    simpa only [HorizontalEstimate.horizontalIntegrand, DirichletCharacter.LFunction_modOne_eq,
      mul_div_assoc, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add] using h
  have hint : (∫ σ in (-1 / 2 : ℝ)..b, (t ^ σ + 7)) ≤
      t ^ b / Real.log t + 7 * (b + 1 / 2) := by
    rw [intervalIntegral.integral_add ((Real.continuous_const_rpow ht0.ne').intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const]
    have heq : (∫ σ in (-1 / 2 : ℝ)..b, t ^ σ) =
        (t ^ b - t ^ (-1 / 2 : ℝ)) / Real.log t := by
      simp_rw [Real.rpow_def_of_pos ht0]
      rw [intervalIntegral.integral_comp_mul_left Real.exp hl0.ne', integral_exp]
      simp only [smul_eq_mul]
      ring
    rw [heq]
    simp only [smul_eq_mul]
    have hpow := Real.rpow_nonneg ht0.le (-1 / 2 : ℝ)
    have hh := div_le_div_of_nonneg_right (show t ^ b - t ^ (-1 / 2 : ℝ) ≤ t ^ b by linarith) hl0.le
    linarith
  rw [norm_horizontalIntegral]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by linarith : (-1 / 2 : ℝ) ≤ b) (Filter.Eventually.of_forall hbound)
    ((continuous_const.mul ((Real.continuous_const_rpow ht0.ne').add continuous_const)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left hint (by positivity))

end LiuWang.Proof.PrincipalPsi.Quantitative
