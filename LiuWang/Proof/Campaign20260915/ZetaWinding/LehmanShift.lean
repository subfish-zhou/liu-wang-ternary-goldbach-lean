import LiuWang.Proof.Campaign20260915.ZetaWinding.TuringEndpoints

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation

def horizontalLogMass (T : ℝ) : ℝ :=
  ∫ x in Set.Ioi (1 / 2 : ℝ), Real.log ‖riemannZeta (horizontalAt T x)‖

theorem zeta_horizontal_log_integrable_Ioi {T : ℝ} (hT : T ≠ 0) (a : ℝ) :
    IntegrableOn (fun x => Real.log ‖riemannZeta (horizontalAt T x)‖) (Set.Ioi a) := by
  have hr : IntegrableOn (fun x => Real.log ‖riemannZeta (horizontalAt T x)‖)
      (Set.Ioi (max a 2)) := by
    simpa only [RCLike.re_to_complex, log_re] using!
      (log_zeta_right_integrable T (le_max_right a 2)).re
  have hf := (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_max_left a 2)).mp
    (zeta_horizontal_log_integrable hT a (max a 2))
  rw [← Set.Ioc_union_Ioi_eq_Ioi (le_max_left a 2)]
  exact hf.union hr

theorem horizontalLogMass_split {T : ℝ} (hT : T ≠ 0) (a : ℝ) :
    horizontalLogMass T =
      (∫ x in (1 / 2 : ℝ)..a, Real.log ‖riemannZeta (horizontalAt T x)‖) +
        ∫ x in Set.Ioi a, Real.log ‖riemannZeta (horizontalAt T x)‖ :=
  (intervalIntegral.integral_interval_add_Ioi
    (zeta_horizontal_log_integrable_Ioi hT (1 / 2))
    (zeta_horizontal_log_integrable_Ioi hT a)).symm

theorem horizontalLogMass_truncation_error {T : ℝ} (hT : T ≠ 0)
    {a : ℝ} (ha : 2 ≤ a) :
    |horizontalLogMass T -
      (∫ x in (1 / 2 : ℝ)..a, Real.log ‖riemannZeta (horizontalAt T x)‖)| ≤
        3 * 2 ^ (2 - a) / Real.log 2 := by
  rw [horizontalLogMass_split hT a, add_sub_cancel_left]
  have he := integral_re (log_zeta_right_integrable T ha)
  simp only [log_re, RCLike.re_to_complex] at he
  rw [he]
  exact (abs_re_le_norm _).trans (norm_integral_log_zeta_right_le T ha)

theorem zeta_shift_one_log_ae (T : ℝ) :
    ∀ᵐ x : ℝ, x ∈ Set.uIoc (1 / 2 : ℝ) (3 / 2) →
      Real.log ‖riemannZeta (horizontalAt T x) /
        riemannZeta (horizontalAt T (x + 1))‖ =
      Real.log ‖riemannZeta (horizontalAt T x)‖ -
        Real.log ‖riemannZeta (horizontalAt T (x + 1))‖ := by
  classical
  let F := (zetaClosedValues |T|).image Complex.re
  filter_upwards [F.finite_toSet.countable.ae_notMem volume] with x hx hxI
  rw [Set.uIoc_of_le (by norm_num)] at hxI
  have hd : riemannZeta (horizontalAt T (x + 1)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp only [horizontalAt, add_re, ofReal_re,
      mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]; linarith [hxI.1])
  have hn : riemannZeta (horizontalAt T x) ≠ 0 := by
    intro hz
    have h1 : x < 1 := by
      by_contra hh
      exact riemannZeta_ne_zero_of_one_le_re
        (s := horizontalAt T x) (by simpa [horizontalAt] using not_lt.mp hh) hz
    have hm : horizontalAt T x ∈ zetaClosedValues |T| :=
      mem_zetaClosedValues.mpr ⟨hz, by simpa [horizontalAt] using (show 0 < x by linarith [hxI.1]),
        by simpa [horizontalAt] using h1, by simp [horizontalAt]⟩
    exact hx (Finset.mem_image.mpr ⟨horizontalAt T x, hm, by simp [horizontalAt]⟩)
  rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hn) (norm_ne_zero_iff.mpr hd)]

theorem zeta_shift_one_log_integrable {T : ℝ} (hT : T ≠ 0) :
    IntervalIntegrable (fun x => Real.log ‖riemannZeta (horizontalAt T x) /
      riemannZeta (horizontalAt T (x + 1))‖) volume (1 / 2) (3 / 2) := by
  have hi : IntervalIntegrable (fun x => Real.log ‖riemannZeta (horizontalAt T (x + 1))‖)
      volume (1 / 2) (3 / 2) := by
    have h := (zeta_horizontal_log_integrable hT (3 / 2) (5 / 2)).comp_add_right 1
    norm_num at h
    exact h
  apply ((zeta_horizontal_log_integrable hT (1 / 2) (3 / 2)).sub hi).congr_ae
  exact (ae_restrict_iff' measurableSet_uIoc).mpr
    ((zeta_shift_one_log_ae T).mono (fun _ h hx => (h hx).symm))

theorem lehman_shift_one_identity {T : ℝ} (hT : T ≠ 0) :
    horizontalLogMass T =
      (∫ x in (1 / 2 : ℝ)..(3 / 2),
        Real.log ‖riemannZeta (horizontalAt T x) /
          riemannZeta (horizontalAt T (x + 1))‖) +
      (∫ x in Set.Ioi (3 / 2 : ℝ), Real.log ‖riemannZeta (horizontalAt T x)‖) +
      (∫ x in (3 / 2 : ℝ)..(5 / 2), Real.log ‖riemannZeta (horizontalAt T x)‖) := by
  have hi : IntervalIntegrable (fun x => Real.log ‖riemannZeta (horizontalAt T (x + 1))‖)
      volume (1 / 2) (3 / 2) := by
    have h := (zeta_horizontal_log_integrable hT (3 / 2) (5 / 2)).comp_add_right 1
    norm_num at h
    exact h
  rw [intervalIntegral.integral_congr_ae (zeta_shift_one_log_ae T),
    intervalIntegral.integral_sub (zeta_horizontal_log_integrable hT (1 / 2) (3 / 2)) hi,
    intervalIntegral.integral_comp_add_right
      (fun x => Real.log ‖riemannZeta (horizontalAt T x)‖) 1,
    horizontalLogMass_split hT (3 / 2)]
  norm_num only [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num,
    show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num]
  ring

theorem polynomial_shift_one_nonneg {T : ℝ} (hT : T ≠ 0) :
    0 ≤ ∫ x in (1 / 2 : ℝ)..(3 / 2),
      Real.log ‖horizontalAt T x / (horizontalAt T x - 1)‖ := by
  have hn (x : ℝ) : horizontalAt T x - 1 ≠ 0 := by
    intro hh
    have hi := congrArg Complex.im hh
    exact hT (by simpa [horizontalAt] using hi)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  have hsq : ‖horizontalAt T x - 1‖ ^ 2 ≤ ‖horizontalAt T x‖ ^ 2 := by
    simp only [← normSq_eq_norm_sq, normSq_apply]
    norm_num [horizontalAt]
    nlinarith [hx.1]
  have hnorm : ‖horizontalAt T x - 1‖ ≤ ‖horizontalAt T x‖ := by
    nlinarith [norm_nonneg (horizontalAt T x - 1), norm_nonneg (horizontalAt T x)]
  apply Real.log_nonneg
  rw [norm_div, le_div_iff₀ (norm_pos_iff.mpr (hn x)), one_mul]
  exact hnorm

#print axioms horizontalLogMass_truncation_error
#print axioms zeta_shift_one_log_integrable
#print axioms lehman_shift_one_identity
#print axioms polynomial_shift_one_nonneg

end LiuWang.Proof.Campaign20260915.ZetaWinding
