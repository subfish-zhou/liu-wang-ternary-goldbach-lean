import LiuWang.Proof.Campaign20260915.RosserCount.BacklundMiddleGrowth
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundOuterReduction

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_circle_height_bounds {T u : ℝ} (hT : rsA ≤ T) (hu : |u| = T)
    {s : ℂ} (hs : ‖s‖ ≤ 33 / 25) :
    1000 ≤ T - 33 / 25 ∧ T - 33 / 25 ≤ |s.im + u| ∧
      |s.im + u| ≤ T + 33 / 25 := by
  have h := Real.pow_div_factorial_le_exp (999 / 100 : ℝ) (by norm_num) 8
  norm_num at h
  have hT' : 2000 ≤ T := by
    change Real.exp (999 / 100) ≤ T at hT
    linarith
  have hi := (abs_im_le_norm s).trans hs
  have hlo := abs_add_le (s.im + u) (-s.im)
  rw [show s.im + u + -s.im = u by ring, abs_neg, hu] at hlo
  have hhi := abs_add_le s.im u
  rw [hu] at hhi
  exact ⟨by linarith, by linarith, by linarith⟩

theorem backlund_middle_branch_log_bound {T u : ℝ} (hT : rsA ≤ T) (hu : |u| = T)
    {s : ℂ} (hs : ‖s‖ ≤ 33 / 25)
    (hre : 0 ≤ s.re + 5 / 4) (hre' : s.re + 5 / 4 ≤ 1) :
    Real.log ‖riemannZeta (s + 5 / 4 + (u : ℂ) * I)‖ ≤
      Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) +
      ((1 - (s.re + 5 / 4)) / 2) * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
      Real.log (Real.log (T + 33 / 25)) := by
  let w := s + 5 / 4 + (u : ℂ) * I
  let X := T - 33 / 25
  let Y := T + 33 / 25
  have hwre : w.re = s.re + 5 / 4 := by simp [w]
  have hwim : w.im = s.im + u := by simp [w]
  have hheight := backlund_circle_height_bounds hT hu hs
  have hX : 1000 ≤ X := hheight.1
  have htlo : X ≤ |w.im| := by simpa only [hwim] using hheight.2.1
  have hthi : |w.im| ≤ Y := by simpa only [hwim] using hheight.2.2
  have ht0 : 0 < |w.im| := by linarith
  have hY0 : 0 < Y := ht0.trans_le hthi
  have hXden : 0 < X ^ 2 - 4 := by nlinarith
  have htden : 0 < |w.im| ^ 2 - 4 := by nlinarith
  have hc : |w.im| ^ 2 / (|w.im| ^ 2 - 4) ≤ X ^ 2 / (X ^ 2 - 4) := by
    rw [div_le_div_iff₀ htden hXden]
    nlinarith
  have hc1 : 1 ≤ X ^ 2 / (X ^ 2 - 4) := by
    rw [le_div_iff₀ hXden]
    linarith
  have hexp : 0 ≤ (1 - w.re) / 2 := by rw [hwre]; linarith
  have hpower : (|w.im| / (2 * Real.pi)) ^ ((1 - w.re) / 2) ≤
      (Y / (2 * Real.pi)) ^ ((1 - w.re) / 2) :=
    Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right hthi (by positivity)) hexp
  have hlog := Real.log_le_log ht0 hthi
  have hlog0 : 0 ≤ Real.log |w.im| := Real.log_nonneg (by linarith)
  have hg := backlund_zeta_middle_growth
    (s := w) (by rwa [hwre]) (by rwa [hwre]) (by linarith)
  have hupper : ‖riemannZeta w‖ <
      (X ^ 2 / (X ^ 2 - 4)) * (Y / (2 * Real.pi)) ^ ((1 - w.re) / 2) *
        Real.log Y := by
    apply hg.trans_le
    exact mul_le_mul (mul_le_mul hc hpower (by positivity) (by positivity))
      hlog hlog0 (by positivity)
  have hbase : 1 ≤ Y / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_four]
  have hlogY : 1 ≤ Real.log Y := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : 3 ≤ Y)
    linarith [Real.log_three_gt_d9]
  change Real.log ‖riemannZeta w‖ ≤ Real.log (X ^ 2 / (X ^ 2 - 4)) +
    ((1 - (s.re + 5 / 4)) / 2) * Real.log (Y / (2 * Real.pi)) + Real.log (Real.log Y)
  rw [← hwre]
  by_cases hz : riemannZeta w = 0
  · rw [hz, norm_zero, Real.log_zero]
    exact add_nonneg (add_nonneg (Real.log_nonneg hc1)
      (mul_nonneg hexp (Real.log_nonneg hbase))) (Real.log_nonneg hlogY)
  · have h := Real.log_le_log (norm_pos_iff.mpr hz) hupper.le
    rw [Real.log_mul (by positivity) (by linarith : Real.log Y ≠ 0),
      Real.log_mul (by positivity) (by positivity),
      Real.rpow_def_of_pos (div_pos hY0 (by positivity)), Real.log_exp] at h
    nlinarith only [h]

theorem backlundCircleEnvelope_middle_le {T : ℝ} (hT : rsA ≤ T)
    {s : ℂ} (hs : ‖s‖ ≤ 33 / 25)
    (hre : 0 ≤ s.re + 5 / 4) (hre' : s.re + 5 / 4 ≤ 1) :
    backlundCircleEnvelope T s ≤
      Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) +
      ((1 - (s.re + 5 / 4)) / 2) * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
      Real.log (Real.log (T + 33 / 25)) := by
  have hT0 : 0 ≤ T := by linarith [rsA_ge_thousand]
  apply max_le
  · exact backlund_middle_branch_log_bound hT (abs_of_nonneg hT0) hs hre hre'
  · simpa only [ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      backlund_middle_branch_log_bound hT
        (show |(-T)| = T by rw [abs_neg, abs_of_nonneg hT0]) hs hre hre'

def backlundExplicitEnvelope (T : ℝ) (s : ℂ) : ℝ :=
  if s.re + 5 / 4 ≤ 0 then
    (1 / 2 - (s.re + 5 / 4)) * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
      Real.log (Real.log (T + 33 / 25))
  else if 1 ≤ s.re + 5 / 4 then Real.log (Real.log (T + 33 / 25))
  else Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) +
    ((1 - (s.re + 5 / 4)) / 2) * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
      Real.log (Real.log (T + 33 / 25))

theorem backlundExplicitEnvelope_circleIntegrable (T : ℝ) :
    CircleIntegrable (backlundExplicitEnvelope T) 0 (33 / 25 : ℝ) := by
  classical
  have hl : MeasurableSet {θ : ℝ | (circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4 ≤ 0} :=
    measurableSet_le (by fun_prop) measurable_const
  have hr : MeasurableSet {θ : ℝ | 1 ≤ (circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4} :=
    measurableSet_le measurable_const (by fun_prop)
  have hc : IntervalIntegrable (fun θ : ℝ =>
      (1 / 2 - ((circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4)) *
        Real.log ((T + 33 / 25) / (2 * Real.pi)) + Real.log (Real.log (T + 33 / 25)))
      volume 0 (2 * Real.pi) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hm : IntervalIntegrable (fun θ : ℝ =>
      Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) +
      ((1 - ((circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4)) / 2) *
        Real.log ((T + 33 / 25) / (2 * Real.pi)) + Real.log (Real.log (T + 33 / 25)))
      volume 0 (2 * Real.pi) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hk : IntervalIntegrable (fun _ : ℝ => Real.log (Real.log (T + 33 / 25)))
      volume 0 (2 * Real.pi) := intervalIntegrable_const
  have hi1 := Integrable.piecewise hr hk.1.integrableOn hm.1.integrableOn
  have hi2 := Integrable.piecewise hr hk.2.integrableOn hm.2.integrableOn
  constructor
  · exact Integrable.piecewise hl hc.1.integrableOn hi1.integrableOn
  · exact Integrable.piecewise hl hc.2.integrableOn hi2.integrableOn

theorem backlundCircleAverage_le_explicit {T : ℝ} (hT : rsA ≤ T) :
    Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) ≤
      Real.circleAverage (backlundExplicitEnvelope T) 0 (33 / 25 : ℝ) := by
  apply Real.circleAverage_mono (backlundCircleEnvelope_circleIntegrable hT)
    (backlundExplicitEnvelope_circleIntegrable T)
  intro s hs
  have hnorm : ‖s‖ = 33 / 25 := by
    simpa only [Metric.mem_sphere, dist_zero_right,
      abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25)] using hs
  unfold backlundExplicitEnvelope
  split_ifs with hl hr
  · exact backlundCircleEnvelope_left_le hT hnorm.le hl
  · exact backlundCircleEnvelope_right_le hT hnorm.le hr
  · exact backlundCircleEnvelope_middle_le hT hnorm.le (le_of_not_ge hl) (le_of_not_ge hr)

theorem positiveCount_backlund_explicit_circle_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (Real.circleAverage (backlundExplicitEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi +
      4 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  have h := div_le_div_of_nonneg_right
    (sub_le_sub_right (backlundCircleAverage_le_explicit hT)
      (Real.log ‖riemannZeta (backlundCenterPoint T)‖))
    (show 0 ≤ 2 * Real.log (44 / 25 : ℝ) by positivity)
  exact (positiveCount_backlund_gamma_paid_bound hT hr).trans_le
    (add_le_add (add_le_add (add_le_add h le_rfl) le_rfl) le_rfl)

#print axioms backlund_circle_height_bounds
#print axioms backlund_middle_branch_log_bound
#print axioms backlundCircleEnvelope_middle_le
#print axioms backlundExplicitEnvelope_circleIntegrable
#print axioms backlundCircleAverage_le_explicit
#print axioms positiveCount_backlund_explicit_circle_bound

end LiuWang.Proof.Campaign20260915.RosserCount
