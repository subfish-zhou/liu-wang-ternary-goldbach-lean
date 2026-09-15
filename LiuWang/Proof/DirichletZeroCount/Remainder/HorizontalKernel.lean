import LiuWang.Proof.DirichletZeroCount.Remainder.RightVertical
import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.CompensatedSum

/-! # Height-gap-independent imaginary integrals of compensated zero kernels -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem reciprocal_im_primitive {rho : ℂ} {H : ℝ} (hH : H - rho.im ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -Real.arctan ((t - rho.re) / (H - rho.im)))
      (1 / ((x : ℂ) + (H : ℂ) * I - rho)).im x := by
  have hd := (((hasDerivAt_id x).sub_const rho.re).div_const (H - rho.im)).arctan.neg
  convert! hd using 1
  simp only [one_div, inv_im, normSq_apply, sub_re, sub_im, add_re, add_im,
    mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, zero_add, mul_one, id_eq]
  field_simp [hH]
  ring

theorem reciprocal_im_integrable {rho : ℂ} {H : ℝ} (hH : H - rho.im ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (1 / ((x : ℂ) + (H : ℂ) * I - rho)).im)
      volume a b := by
  apply Continuous.intervalIntegrable
  apply continuous_im.comp
  apply continuous_const.div (by fun_prop)
  intro x he
  apply hH
  have hx := congrArg Complex.im he
  simpa using hx

theorem reciprocal_im_integral_abs_le_pi {rho : ℂ} {H : ℝ}
    (hH : H - rho.im ≠ 0) (a b : ℝ) :
    |∫ x in a..b, (1 / ((x : ℂ) + (H : ℂ) * I - rho)).im| ≤ Real.pi := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => reciprocal_im_primitive hH x) (reciprocal_im_integrable hH a b)]
  have h (x : ℝ) : |Real.arctan x| < Real.pi / 2 :=
    abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan x, Real.arctan_lt_pi_div_two x⟩
  apply (abs_sub _ _).trans
  simp only [abs_neg]
  linarith [h ((a - rho.re) / (H - rho.im)), h ((b - rho.re) / (H - rho.im))]

theorem compensated_im_integral_le_kernel {rho : ℂ} {H : ℝ}
    (hrho : rho.re ∈ Set.Icc 0 1) (hH : H - rho.im ≠ 0) :
    |∫ x in (1 / 2 : ℝ)..2,
      (1 / ((x : ℂ) + (H : ℂ) * I - rho) - 1 / (referencePoint H - rho)).im| ≤
      (5 * Real.pi / 2 + 4) * (1 / (referencePoint H - rho)).re := by
  let K : ℝ := (1 / (referencePoint H - rho)).re
  have hk : 0 ≤ K := by
    dsimp [K]
    rw [one_div, inv_re]
    apply div_nonneg
    · simpa [referencePoint] using (show 0 ≤ 2 - rho.re by linarith [hrho.2])
    · exact normSq_nonneg _
  have hri := reciprocal_im_integrable hH (1 / 2) 2
  have hci : IntervalIntegrable (fun x : ℝ =>
      (1 / ((x : ℂ) + (H : ℂ) * I - rho) - 1 / (referencePoint H - rho)).im)
      volume (1 / 2) 2 := by
    simpa only [sub_im] using hri.sub intervalIntegrable_const
  by_cases hnear : |H - rho.im| ≤ 1
  · have hlow := two_fifths_le_reference_kernel hrho hnear
    have hn : 1 ≤ ‖referencePoint H - rho‖ := by
      have hh : 2 - rho.re ≤ ‖referencePoint H - rho‖ := by
        simpa [referencePoint] using re_le_norm (referencePoint H - rho)
      linarith [hrho.2]
    have hnorm : ‖1 / (referencePoint H - rho)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      exact (div_le_one (by linarith)).mpr hn
    have hbd := (abs_im_le_norm (1 / (referencePoint H - rho))).trans hnorm
    simp_rw [sub_im]
    rw [intervalIntegral.integral_sub hri intervalIntegrable_const,
      intervalIntegral.integral_const]
    have hab := reciprocal_im_integral_abs_le_pi hH (1 / 2) 2
    have he : |(2 - (1 / 2 : ℝ)) • (1 / (referencePoint H - rho)).im| ≤ 3 / 2 := by
      simp only [smul_eq_mul, abs_mul]
      norm_num only [show 2 - (1 / 2 : ℝ) = 3 / 2 by norm_num,
        abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      linarith
    apply (abs_sub _ _).trans
    change _ ≤ (5 * Real.pi / 2 + 4) * K
    change 2 / 5 ≤ K at hlow
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hlow)]
  · have hsep : (1 : ℝ)⁻¹ ≤ |rho.im - H| := by
      rw [abs_sub_comm]
      simpa using (not_le.mp hnear).le
    have hpoint (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
        |(1 / ((x : ℂ) + (H : ℂ) * I - rho) - 1 / (referencePoint H - rho)).im| ≤ (15 / 4) * K := by
      apply (abs_im_le_norm _).trans
      have hp := norm_reciprocal_difference_le_reference_kernel (s := (x : ℂ) + (H : ℂ) * I)
        (by norm_num : (0 : ℝ) < 1) hsep (by simp)
        (by norm_num : (0 : ℝ) ≤ 3 / 2) (by simp; linarith [hx.1]) (by simpa using hx.2) hrho
      norm_num only [show (3 / 2 : ℝ) + (3 / 2) ^ 2 * 1 = 15 / 4 by norm_num] at hp
      exact hp
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 / 2 : ℝ)) (b := 2) (C := (15 / 4) * K)
      (f := fun x : ℝ => (1 / ((x : ℂ) + (H : ℂ) * I - rho) - 1 / (referencePoint H - rho)).im)
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num)] at hx
        simpa only [Real.norm_eq_abs] using hpoint x ⟨hx.1.le, hx.2⟩)
    rw [Real.norm_eq_abs] at hb
    norm_num only [show 2 - (1 / 2 : ℝ) = 3 / 2 by norm_num,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hb
    change _ ≤ (5 * Real.pi / 2 + 4) * K
    nlinarith [Real.pi_gt_three]

end LiuWang.Proof.DirichletZeroCount.Remainder
