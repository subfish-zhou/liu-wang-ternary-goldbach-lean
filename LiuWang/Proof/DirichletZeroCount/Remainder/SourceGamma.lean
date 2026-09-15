import LiuWang.Proof.DirichletZeroCount.Remainder.GammaUpper

/-! # Literal source Gamma phase, with a stronger nonpositive remainder -/

set_option autoImplicit false
noncomputable section
open Complex Filter MeasureTheory
open scoped Topology Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def sourceGammaMain (a H : ℝ) : ℝ :=
  H * Real.log (‖(a : ℂ) + (H : ℂ) * I‖ / 2) - H +
    (a - 1) * Real.arctan (H / a)

theorem arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) :=
  (Real.arctan_eq_of_tan_eq (tan_arg z)
    (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)))).symm

theorem gammaPhaseMain_eq_source {a H : ℝ} (ha : 0 < a) :
    gammaPhaseMain a H = sourceGammaMain a H := by
  have hz : 0 < (((a : ℂ) + (H : ℂ) * I) / 2).re := by simpa using half_pos ha
  have harg := arg_eq_arctan_of_re_pos hz
  simp only [div_ofNat_im, div_ofNat_re, add_re, add_im, mul_re, mul_im,
    ofReal_re, ofReal_im, I_re, I_im, mul_zero, sub_zero, add_zero,
    zero_add, mul_one, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)] at harg
  unfold gammaPhaseMain stirlingPhase sourceGammaMain
  simp only [sub_im, mul_im, sub_re, div_ofNat_re, div_ofNat_im,
    add_re, add_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
    zero_div, sub_zero, add_zero, zero_add, mul_one, one_re, one_im, log_re, log_im]
  rw [harg, norm_div]
  norm_num
  ring

theorem digammaVertical_le_sourceGammaMain {a H : ℝ} (ha : 0 < a) (hH : 0 ≤ H) :
    Argument.digammaVertical a H ≤ sourceGammaMain a H := by
  rw [← gammaPhaseMain_eq_source ha]
  exact digammaVertical_le_main ha hH

theorem digammaVertical_le_source331 {a H : ℝ} (ha : 0 < a) (hH : 0 ≤ H) :
    Argument.digammaVertical a H ≤ sourceGammaMain a H +
      Real.pi / (4 * ‖(a : ℂ) + (H : ℂ) * I‖) :=
  (digammaVertical_le_sourceGammaMain ha hH).trans (le_add_of_nonneg_right (by positivity))

theorem sourceGammaMain_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (sourceGammaMain a) := by
  have he : sourceGammaMain a = gammaPhaseMain a :=
    funext fun _ => (gammaPhaseMain_eq_source ha).symm
  rw [he]
  exact gammaPhaseMain_continuous ha

theorem sourceGammaMain_zero {a : ℝ} (ha : 0 < a) : sourceGammaMain a 0 = 0 := by
  rw [← gammaPhaseMain_eq_source ha, gammaPhaseMain_zero a ha]

theorem gamma_three_im_le_source {q : ℕ} (chi : Character q) {b H : ℝ}
    (hb : 1 < b) (hH : 0 ≤ H) :
    (Argument.rightThreeIntegral (logDeriv chi.gammaFactor) b H).im ≤
      -H * Real.log Real.pi +
        (if chi.Even then sourceGammaMain (1 / 2) H else sourceGammaMain (3 / 2) H) := by
  rcases chi.even_or_odd with he | ho
  · rw [if_pos he, Argument.gamma_three_im_even he hb hH]
    exact add_le_add_right (digammaVertical_le_sourceGammaMain (by norm_num) hH) _
  · rw [if_neg ho.not_even, Argument.gamma_three_im_odd ho hb hH]
    exact add_le_add_right (digammaVertical_le_sourceGammaMain (by norm_num) hH) _

theorem completed_count_le_sourceGamma {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    (count chi 0 H : ℝ) ≤
      (H * Real.log ((q : ℝ) / Real.pi) +
        (Argument.rightThreeIntegral (logDeriv chi.LFunction) b H).im +
        (if chi.Even then sourceGammaMain (1 / 2) H else sourceGammaMain (3 / 2) H)) / Real.pi := by
  simpa only [gammaPhaseMain_eq_source (by norm_num : (0 : ℝ) < 1 / 2),
    gammaPhaseMain_eq_source (by norm_num : (0 : ℝ) < 3 / 2)] using
    completed_count_le_gamma_main hchi hprim hb hH hreg

end LiuWang.Proof.DirichletZeroCount.Remainder
