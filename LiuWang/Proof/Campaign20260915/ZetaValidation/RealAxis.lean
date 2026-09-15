import LiuWang.Proof.Campaign20260915.ZetaValidation.AbelEvaluation

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem zeta_real_re_neg_of_abel_domain {x : ℝ} (hx : 1 / 10 < x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  have hx0 : 0 < x := by linarith
  have hxc1 : (x : ℂ) ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [ofReal_re, one_re] at hh
    linarith
  let J : ℝ := ∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-x - 1)
  have hJ : 0 ≤ J := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hu)) _)
  have hi : (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (x : ℂ) u) = (J : ℂ) := by
    dsimp [J]
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have he : -(x : ℂ) - 1 = ((-x - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [zetaAbelFractKernel, he,
      ← Complex.ofReal_cpow (zero_le_one.trans (le_of_lt hu)), ofReal_mul]
  have he : riemannZeta (x : ℂ) = ((1 + 1 / (x - 1) - x * J : ℝ) : ℂ) := by
    rw [riemannZeta_eq_zetaAbelContinuationFormula (x : ℂ) ⟨hxc1, hx⟩,
      zetaAbelContinuationFormula, hi]
    push_cast
    rfl
  have hr := congrArg Complex.re he
  simp only [ofReal_re] at hr
  rw [hr]
  have hm : 1 + 1 / (x - 1) = x / (x - 1) := by
    field_simp [sub_ne_zero.mpr hx1.ne]
    ring
  rw [hm]
  have hneg : x / (x - 1) < 0 := div_neg_of_pos_of_neg hx0 (by linarith)
  linarith [mul_nonneg hx0.le hJ]

theorem zeta_zero_reflection_of_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  have hsz : s ≠ 0 := by
    intro h
    simp [h] at hs0
  have hso : s ≠ 1 := by
    intro h
    simp [h] at hs1
  rw [riemannZeta_def_of_ne_zero hsz] at hz
  have hc := (div_eq_zero_iff.mp hz).resolve_right (Gammaℝ_ne_zero_of_re_pos hs0)
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr hso.symm),
    completedRiemannZeta_one_sub, hc, zero_div]

theorem zeta_real_ne_zero_of_strip {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  intro hz
  by_cases hx : 1 / 10 < x
  · have h := zeta_real_re_neg_of_abel_domain hx hx1
    rw [hz, zero_re] at h
    exact (lt_irrefl 0) h
  · have h := zeta_real_re_neg_of_abel_domain (x := 1 - x) (by linarith) (by linarith)
    have hr := zeta_zero_reflection_of_strip
      (s := (x : ℂ)) (by simpa using hx0) (by simpa using hx1) hz
    have he : ((1 - x : ℝ) : ℂ) = 1 - (x : ℂ) := by push_cast; rfl
    rw [he, hr, zero_re] at h
    exact (lt_irrefl 0) h

theorem zeta_ne_zero_of_real_axis_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (him : s.im = 0) : riemannZeta s ≠ 0 := by
  have he : s = (s.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [he]
  exact zeta_real_ne_zero_of_strip hs0 hs1

theorem strip_zeta_zero_im_ne_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) : s.im ≠ 0 := by
  intro him
  exact zeta_ne_zero_of_real_axis_strip hs0 hs1 him hz

#print axioms zeta_real_re_neg_of_abel_domain
#print axioms zeta_ne_zero_of_real_axis_strip
#print axioms strip_zeta_zero_im_ne_zero

end LiuWang.Proof.Campaign20260915.ZetaValidation
