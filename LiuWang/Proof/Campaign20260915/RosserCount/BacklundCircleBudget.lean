import LiuWang.Proof.Campaign20260915.RosserCount.BacklundLeftBudget
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightPaidCount

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlundLeftCoefficient_eq (θ : ℝ) :
    backlundLeftCoefficient θ =
      if (circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4 ≤ 0 then
        1 / 2 - ((circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4)
      else if 1 ≤ (circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4 then 0
      else (1 - ((circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4)) / 2 := by
  rw [circleMap_zero_re]
  unfold backlundLeftCoefficient
  split_ifs with hl hr
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    norm_num
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

theorem backlundExplicitEnvelope_majorant {T : ℝ} (hT : rsA ≤ T) (θ : ℝ) :
    backlundExplicitEnvelope T (circleMap 0 (33 / 25 : ℝ) θ) ≤
      backlundLeftCoefficient θ * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
        (Real.log (Real.log (T + 33 / 25)) +
          Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4))) := by
  have hT' : 1000 ≤ T := rsA_ge_thousand.trans hT
  have hden : 0 < (T - 33 / 25) ^ 2 - 4 := by nlinarith
  have hc : 0 ≤ Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hden]
    linarith
  unfold backlundExplicitEnvelope
  rw [backlundLeftCoefficient_eq]
  split_ifs <;> nlinarith

theorem backlund_explicit_left_integral_bound {T : ℝ} (hT : rsA ≤ T) :
    (∫ θ in Real.pi / 2..Real.pi,
      backlundExplicitEnvelope T (circleMap 0 (33 / 25 : ℝ) θ)) ≤
      Real.pi * ((77 / 500) * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
        (1 / 2) * Real.log (Real.log (T + 33 / 25)) +
        (1 / 2) * Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4))) := by
  let L := Real.log ((T + 33 / 25) / (2 * Real.pi))
  let B := Real.log (Real.log (T + 33 / 25)) +
    Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4))
  have hT' : 1000 ≤ T := rsA_ge_thousand.trans hT
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_four]
  have hp : Real.pi / 2 ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := by
    rw [Set.uIcc_of_le (by positivity)]
    constructor <;> linarith [Real.pi_pos]
  have hp' : Real.pi ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := by
    rw [Set.uIcc_of_le (by positivity)]
    constructor <;> linarith [Real.pi_pos]
  have he := (backlundExplicitEnvelope_circleIntegrable T).mono_set
    (Set.uIcc_subset_uIcc hp hp')
  have hc : Continuous (fun θ : ℝ => backlundLeftCoefficient θ * L) :=
    backlundLeftCoefficient_continuous.mul continuous_const
  have hi : IntervalIntegrable (fun θ : ℝ => backlundLeftCoefficient θ * L + B)
      volume (Real.pi / 2) Real.pi :=
    (hc.add continuous_const).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) he hi
    (fun θ _ => backlundExplicitEnvelope_majorant hT θ)
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_const] at hm
  have hb := mul_le_mul_of_nonneg_right backlund_left_coefficient_budget hL
  dsimp [L, B] at hm hb
  nlinarith

def backlundCircleBudget (T : ℝ) : ℝ :=
  5471 / 20000 + (77 / 500) * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
    (1 / 2) * Real.log (Real.log (T + 33 / 25)) +
    (1 / 2) * Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4))

theorem backlundCircleAverage_numerical_bound {T : ℝ} (hT : rsA ≤ T) :
    Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) ≤
      backlundCircleBudget T := by
  have hi := mul_le_mul_of_nonneg_left (backlund_explicit_left_integral_bound hT)
    (show (0 : ℝ) ≤ 1 / Real.pi by positivity)
  have hs : 5471 / 20000 + (1 / Real.pi) *
      (∫ θ in Real.pi / 2..Real.pi,
        backlundExplicitEnvelope T (circleMap 0 (33 / 25 : ℝ) θ)) ≤
        backlundCircleBudget T := by
    unfold backlundCircleBudget
    simpa [← mul_assoc, Real.pi_ne_zero, add_assoc] using
      (add_le_add (le_rfl : (5471 / 20000 : ℝ) ≤ 5471 / 20000) hi)
  exact (backlundCircleAverage_right_budget hT).trans hs

theorem positiveCount_backlund_numerical_circle_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (backlundCircleBudget T - Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi +
      4 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  have h := div_le_div_of_nonneg_right
    (sub_le_sub_right (backlundCircleAverage_numerical_bound hT)
      (Real.log ‖riemannZeta (backlundCenterPoint T)‖))
    (show 0 ≤ 2 * Real.log (44 / 25 : ℝ) by positivity)
  exact (positiveCount_backlund_gamma_paid_bound hT hr).trans_le
    (add_le_add (add_le_add (add_le_add h le_rfl) le_rfl) le_rfl)

#print axioms backlundLeftCoefficient_eq
#print axioms backlundExplicitEnvelope_majorant
#print axioms backlund_explicit_left_integral_bound
#print axioms backlundCircleAverage_numerical_bound
#print axioms positiveCount_backlund_numerical_circle_bound

end LiuWang.Proof.Campaign20260915.RosserCount
