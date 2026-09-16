import LiuWang.Proof.Campaign20260915.RosserCount.BacklundScalarBounds

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlundCountBudget_lt_rosserError {T : ℝ} (hT : rsA ≤ T) :
    backlundCountBudget T < rosserError T := by
  have hT' : 1000 ≤ T := rsA_ge_thousand.trans hT
  have hT0 : 0 < T := by linarith
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hq := backlund_jensen_log_lower
  have hq0 : 0 < 2 * Real.log (44 / 25 : ℝ) := by linarith
  obtain ⟨hlog, hshift, hdouble, hcorrection⟩ := backlund_shifted_log_bounds hT'
  have hloglog : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlog
  let M := (77 / 500 : ℝ) * Real.log T + (1 / 2) * Real.log (Real.log T) + 247 / 200
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hnum : backlundCircleBudget T - Real.log ‖riemannZeta (backlundCenterPoint T)‖ ≤ M := by
    unfold backlundCircleBudget
    rw [Real.log_div (by positivity : T + 33 / 25 ≠ 0) (by positivity : 2 * Real.pi ≠ 0)]
    dsimp [M]
    linarith [backlund_log_two_pi_lower, backlund_center_log_numeric T]
  have hmain : (backlundCircleBudget T - Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
      (2 * Real.log (44 / 25 : ℝ)) ≤ M / (113 / 100) :=
    (div_le_div_of_nonneg_right hnum hq0.le).trans
      (div_le_div_of_nonneg_left hM (by norm_num) (by linarith))
  have hphase : Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi ≤
      (3821 / 2500 : ℝ) / (157 / 50) :=
    (div_le_div_of_nonneg_right backlund_real_center_log_upper Real.pi_pos.le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp)
  have hden : (3140 : ℝ) ≤ Real.pi * T := by
    nlinarith [mul_le_mul_of_nonneg_left hT' Real.pi_pos.le]
  have hfour : 4 / (Real.pi * T) ≤ (4 / 3140 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
  have hquarter : 1 / (4 * Real.pi * T) ≤ (1 / 12560 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have htotal : M / (113 / 100) + (3821 / 2500 : ℝ) / (157 / 50) +
      4 / 3140 + 1 / 12560 < rosserError T := by
    unfold rosserError
    dsimp [M]
    nlinarith
  exact (show backlundCountBudget T ≤
      M / (113 / 100) + (3821 / 2500 : ℝ) / (157 / 50) + 4 / 3140 + 1 / 12560 from
    add_le_add (add_le_add (add_le_add hmain hphase) hfour) hquarter).trans_lt htotal

theorem positiveCount_original_rosser_bound {T : ℝ} (hT : rsA ≤ T) :
    |(positiveCount T : ℝ) - rosserMain T| < rosserError T :=
  (positiveCount_backlund_closed_numerical_bound hT).trans_lt
    (backlundCountBudget_lt_rosserError hT)

#print axioms backlundCountBudget_lt_rosserError
#print axioms positiveCount_original_rosser_bound

end LiuWang.Proof.Campaign20260915.RosserCount
