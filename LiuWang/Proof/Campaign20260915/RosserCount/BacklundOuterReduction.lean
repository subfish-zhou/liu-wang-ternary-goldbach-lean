import LiuWang.Proof.Campaign20260915.RosserCount.BacklundLeftGrowth
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightReduction

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_zeta_left_growth {s : ℂ}
    (hs : -(1 / 2 : ℝ) ≤ s.re) (hs' : s.re ≤ 0) (ht : 1000 ≤ |s.im|) :
    ‖riemannZeta s‖ <
      (|s.im| / (2 * Real.pi)) ^ (1 / 2 - s.re) * Real.log |s.im| := by
  by_cases hy : 0 ≤ s.im
  · have he : horizontalAt s.im s.re = s := by
      apply Complex.ext <;> simp [horizontalAt]
    simpa only [he, abs_of_nonneg hy] using
      backlund_zeta_left_growth_positive (t := s.im) hs hs'
        (by rwa [abs_of_nonneg hy] at ht)
  · have he : horizontalAt (-s.im) s.re = conj s := by
      apply Complex.ext <;> simp [horizontalAt]
    have h := backlund_zeta_left_growth_positive (t := -s.im) hs hs'
      (by rwa [abs_of_neg (lt_of_not_ge hy)] at ht)
    simpa only [he, riemannZeta_conj, norm_conj, abs_of_neg (lt_of_not_ge hy)] using h

private theorem backlund_circle_height_range {T u : ℝ} (hT : rsA ≤ T) (hu : |u| = T)
    {s : ℂ} (hs : ‖s‖ ≤ 33 / 25) :
    1000 ≤ |s.im + u| ∧ |s.im + u| ≤ T + 33 / 25 := by
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
  constructor <;> linarith

theorem backlund_left_branch_log_bound {T u : ℝ} (hT : rsA ≤ T) (hu : |u| = T)
    {s : ℂ} (hs : ‖s‖ ≤ 33 / 25) (hre : s.re + 5 / 4 ≤ 0) :
    Real.log ‖riemannZeta (s + 5 / 4 + (u : ℂ) * I)‖ ≤
      (1 / 2 - (s.re + 5 / 4)) * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
        Real.log (Real.log (T + 33 / 25)) := by
  let w := s + 5 / 4 + (u : ℂ) * I
  let Y := T + 33 / 25
  have hwre : w.re = s.re + 5 / 4 := by simp [w]
  have hwim : w.im = s.im + u := by simp [w]
  have ht := backlund_circle_height_range hT hu hs
  have hy0 : 0 < |w.im| := by rw [hwim]; linarith [ht.1]
  have hY : |w.im| ≤ Y := by simpa only [hwim] using ht.2
  have hY0 : 0 < Y := hy0.trans_le hY
  have hd : 0 ≤ 1 / 2 - w.re := by rw [hwre]; linarith
  have hlow := (abs_le.mp ((abs_re_le_norm s).trans hs)).1
  have hz := backlund_zeta_left_growth (s := w)
    (by rw [hwre]; linarith) (by rw [hwre]; exact hre) (by rw [hwim]; exact ht.1)
  have hm :
      (|w.im| / (2 * Real.pi)) ^ (1 / 2 - w.re) * Real.log |w.im| ≤
        (Y / (2 * Real.pi)) ^ (1 / 2 - w.re) * Real.log Y := by
    apply mul_le_mul
    · exact Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right hY (by positivity)) hd
    · exact Real.log_le_log hy0 hY
    · exact Real.log_nonneg (by rw [hwim]; linarith [ht.1])
    · positivity
  have hbase : 1 ≤ Y / (2 * Real.pi) := by
    apply (le_div_iff₀ (by positivity)).mpr
    dsimp [Y]
    linarith [rsA_ge_thousand, Real.pi_lt_four]
  have hlogY : 1 ≤ Real.log Y := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ Y by dsimp [Y]; linarith [rsA_ge_thousand])
    linarith [Real.log_three_gt_d9]
  change Real.log ‖riemannZeta w‖ ≤
    (1 / 2 - (s.re + 5 / 4)) * Real.log (Y / (2 * Real.pi)) + Real.log (Real.log Y)
  rw [← hwre]
  by_cases hzero : riemannZeta w = 0
  · rw [hzero, norm_zero, Real.log_zero]
    exact add_nonneg (mul_nonneg hd (Real.log_nonneg hbase)) (Real.log_nonneg hlogY)
  · have h := Real.log_le_log (norm_pos_iff.mpr hzero) (hz.le.trans hm)
    rw [Real.log_mul (by positivity) (by linarith : Real.log Y ≠ 0),
      Real.rpow_def_of_pos (div_pos hY0 (by positivity)), Real.log_exp] at h
    nlinarith only [h]

theorem backlundCircleEnvelope_left_le {T : ℝ} (hT : rsA ≤ T)
    {s : ℂ} (hs : ‖s‖ ≤ 33 / 25) (hre : s.re + 5 / 4 ≤ 0) :
    backlundCircleEnvelope T s ≤
      (1 / 2 - (s.re + 5 / 4)) * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
        Real.log (Real.log (T + 33 / 25)) := by
  have hT0 : 0 ≤ T := by linarith [rsA_ge_thousand]
  apply max_le
  · exact backlund_left_branch_log_bound hT (abs_of_nonneg hT0) hs hre
  · simpa only [ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      backlund_left_branch_log_bound hT
        (show |(-T)| = T by rw [abs_neg, abs_of_nonneg hT0]) hs hre

def backlundOuterEnvelope (T : ℝ) (s : ℂ) : ℝ :=
  if s.re + 5 / 4 ≤ 0 then
    (1 / 2 - (s.re + 5 / 4)) * Real.log ((T + 33 / 25) / (2 * Real.pi)) +
      Real.log (Real.log (T + 33 / 25))
  else backlundRightReducedEnvelope T s

theorem backlundOuterEnvelope_circleIntegrable {T : ℝ} (hT : rsA ≤ T) :
    CircleIntegrable (backlundOuterEnvelope T) 0 (33 / 25 : ℝ) := by
  classical
  have hm : MeasurableSet {θ : ℝ | (circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4 ≤ 0} :=
    measurableSet_le (by fun_prop) measurable_const
  have hc : IntervalIntegrable (fun θ : ℝ =>
      (1 / 2 - ((circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4)) *
        Real.log ((T + 33 / 25) / (2 * Real.pi)) + Real.log (Real.log (T + 33 / 25)))
      volume 0 (2 * Real.pi) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have he := backlundRightReducedEnvelope_circleIntegrable hT
  constructor
  · exact Integrable.piecewise hm hc.1.integrableOn he.1.integrableOn
  · exact Integrable.piecewise hm hc.2.integrableOn he.2.integrableOn

theorem backlundCircleAverage_le_outer {T : ℝ} (hT : rsA ≤ T) :
    Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) ≤
      Real.circleAverage (backlundOuterEnvelope T) 0 (33 / 25 : ℝ) := by
  apply Real.circleAverage_mono (backlundCircleEnvelope_circleIntegrable hT)
    (backlundOuterEnvelope_circleIntegrable hT)
  intro s hs
  have hnorm : ‖s‖ = 33 / 25 := by
    simpa only [Metric.mem_sphere, dist_zero_right,
      abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25)] using hs
  unfold backlundOuterEnvelope backlundRightReducedEnvelope
  split_ifs with hl hr
  · exact backlundCircleEnvelope_left_le hT hnorm.le hl
  · exact backlundCircleEnvelope_right_le hT hnorm.le hr
  · exact le_rfl

theorem positiveCount_backlund_outer_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (Real.circleAverage (backlundOuterEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi +
      4 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  have h := div_le_div_of_nonneg_right
    (sub_le_sub_right (backlundCircleAverage_le_outer hT)
      (Real.log ‖riemannZeta (backlundCenterPoint T)‖))
    (show 0 ≤ 2 * Real.log (44 / 25 : ℝ) by positivity)
  exact (positiveCount_backlund_gamma_paid_bound hT hr).trans_le
    (add_le_add (add_le_add (add_le_add h le_rfl) le_rfl) le_rfl)

#print axioms backlund_zeta_left_growth
#print axioms backlund_left_branch_log_bound
#print axioms backlundCircleEnvelope_left_le
#print axioms backlundOuterEnvelope_circleIntegrable
#print axioms backlundCircleAverage_le_outer
#print axioms positiveCount_backlund_outer_bound

end LiuWang.Proof.Campaign20260915.RosserCount
