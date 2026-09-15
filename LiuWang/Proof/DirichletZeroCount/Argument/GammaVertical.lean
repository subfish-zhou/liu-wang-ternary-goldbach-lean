import LiuWang.Proof.DirichletZeroCount.Argument.GammaSplit
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivative
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-! # Collapse only the zero-free Gamma path, never the completed-L path -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical
open LiuWang.Proof.Interfaces (Character)
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Argument

theorem gamma_three_eq_vertical {q : ℕ} (chi : Character q) {b H : ℝ}
    (hb : 1 < b) (hH : 0 ≤ H) :
    rightThreeIntegral (logDeriv chi.gammaFactor) b H =
      VIntegral (logDeriv chi.gammaFactor) (1 / 2) (-H) H := by
  have hg : HolomorphicOn (logDeriv chi.gammaFactor) {s : ℂ | 0 < s.re} := by
    intro s hs
    have ha := gammaFactor_analyticAt chi hs
    exact (ha.deriv.div ha (DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hs)).differentiableAt.differentiableWithinAt
  have hzre : (((1 / 2 : ℝ) : ℂ) + (-H : ℝ) * I).re ≤ (upperCorner b H).re := by
    simp [upperCorner]
    linarith
  have hzim : (((1 / 2 : ℝ) : ℂ) + (-H : ℝ) * I).im ≤ (upperCorner b H).im := by
    simp [upperCorner]
    linarith
  have he := hg.vanishesOnRectangle
    (z := ((1 / 2 : ℝ) : ℂ) + (-H : ℝ) * I) (w := upperCorner b H) (by
      intro s hs
      have h := (mem_Rect hzre hzim s).mp hs
      have hx : (1 / 2 : ℝ) ≤ s.re := by simpa using h.1
      exact lt_of_lt_of_le (by norm_num) hx)
  simp only [RectangleIntegral, upperCorner, add_re, add_im, ofReal_re, ofReal_im,
    mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at he
  unfold rightThreeIntegral
  linear_combination he

theorem gamma_vertical_im {q : ℕ} (chi : Character q) (H : ℝ) :
    (VIntegral (logDeriv chi.gammaFactor) (1 / 2) (-H) H).im =
      ∫ t in -H..H, (logDeriv chi.gammaFactor (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re := by
  have hc : Continuous (fun t : ℝ => logDeriv chi.gammaFactor
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hs : 0 < (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re := by norm_num
    have ha := gammaFactor_analyticAt chi hs
    exact (ha.deriv.div ha (DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hs)).continuousAt.comp
      (f := fun x : ℝ => ((1 / 2 : ℝ) : ℂ) + (x : ℂ) * I) (by fun_prop)
  simp only [VIntegral, smul_eq_mul, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  exact (intervalIntegral.intervalIntegral_re (hc.intervalIntegrable (-H) H)).symm

def digammaVertical (a H : ℝ) : ℝ :=
  (1 / 2) * ∫ t in -H..H, (digamma (((a : ℂ) + (t : ℂ) * I) / 2)).re

theorem digammaVertical_integrable {a : ℝ} (ha : 0 < a) (H : ℝ) :
    IntervalIntegrable (fun t : ℝ => (digamma (((a : ℂ) + (t : ℂ) * I) / 2)).re)
      volume (-H) H := by
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : 0 < (((a : ℂ) + (t : ℂ) * I) / 2).re := by
    simp only [div_ofNat_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  exact continuous_re.continuousAt.comp ((continuousAt_digamma_of_re_pos hs).comp
    (f := fun x : ℝ => ((a : ℂ) + (x : ℂ) * I) / 2) (by fun_prop))

theorem gamma_three_im_even {q : ℕ} {chi : Character q} (hEven : chi.Even)
    {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H) :
    (rightThreeIntegral (logDeriv chi.gammaFactor) b H).im =
      -H * Real.log Real.pi + digammaVertical (1 / 2) H := by
  rw [gamma_three_eq_vertical chi hb hH, gamma_vertical_im]
  have hp (t : ℝ) :
      (logDeriv chi.gammaFactor (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re =
        -Real.log Real.pi / 2 +
          (1 / 2) * (digamma ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2)).re := by
    rw [logDeriv_gammaFactor_of_even hEven (by norm_num)]
    simp
  simp_rw [hp]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((digammaVertical_integrable (by norm_num : (0 : ℝ) < 1 / 2) H).const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  simp only [digammaVertical, smul_eq_mul]
  ring

theorem gamma_three_im_odd {q : ℕ} {chi : Character q} (hOdd : chi.Odd)
    {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H) :
    (rightThreeIntegral (logDeriv chi.gammaFactor) b H).im =
      -H * Real.log Real.pi + digammaVertical (3 / 2) H := by
  rw [gamma_three_eq_vertical chi hb hH, gamma_vertical_im]
  have hp (t : ℝ) :
      (logDeriv chi.gammaFactor (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re =
        -Real.log Real.pi / 2 +
          (1 / 2) * (digamma ((((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2)).re := by
    rw [logDeriv_gammaFactor_of_odd hOdd (by norm_num)]
    have hs : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I + 1) =
        (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by push_cast; ring
    rw [hs]
    simp
  simp_rw [hp]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((digammaVertical_integrable (by norm_num : (0 : ℝ) < 3 / 2) H).const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  simp only [digammaVertical, smul_eq_mul]
  ring

theorem completed_count_digamma {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    (count chi 0 H : ℝ) =
      (H * Real.log ((q : ℝ) / Real.pi) +
        (rightThreeIntegral (logDeriv chi.LFunction) b H).im +
        (if chi.Even then digammaVertical (1 / 2) H else digammaVertical (3 / 2) H)) /
          Real.pi := by
  rw [completed_count_gamma_split hchi hprim hb hH hreg,
    Real.log_div (by exact_mod_cast NeZero.ne q) Real.pi_ne_zero]
  rcases chi.even_or_odd with he | ho
  · rw [if_pos he, gamma_three_im_even he hb hH]
    ring
  · rw [if_neg ho.not_even, gamma_three_im_odd ho hb hH]
    ring

end LiuWang.Proof.DirichletZeroCount.Argument
