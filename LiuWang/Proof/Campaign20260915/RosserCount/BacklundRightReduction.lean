import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCircle
import LiuWang.Proof.Campaign20260915.RosserCount.RosserGammaBudget

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundRightReducedEnvelope (T : ℝ) (s : ℂ) : ℝ :=
  if 1 ≤ s.re + 5 / 4 then Real.log (Real.log (T + 33 / 25))
  else backlundCircleEnvelope T s

theorem backlundRightReducedEnvelope_circleIntegrable {T : ℝ} (hT : rsA ≤ T) :
    CircleIntegrable (backlundRightReducedEnvelope T) 0 (33 / 25 : ℝ) := by
  classical
  have hm : MeasurableSet {θ : ℝ | 1 ≤ (circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4} :=
    measurableSet_le measurable_const (by fun_prop)
  have hc : IntervalIntegrable (fun _ : ℝ => Real.log (Real.log (T + 33 / 25)))
      volume 0 (2 * Real.pi) := intervalIntegrable_const
  have he := backlundCircleEnvelope_circleIntegrable hT
  constructor
  · exact Integrable.piecewise hm hc.1.integrableOn he.1.integrableOn
  · exact Integrable.piecewise hm hc.2.integrableOn he.2.integrableOn

theorem backlundCircleAverage_le_right_reduced {T : ℝ} (hT : rsA ≤ T) :
    Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) ≤
      Real.circleAverage (backlundRightReducedEnvelope T) 0 (33 / 25 : ℝ) := by
  apply Real.circleAverage_mono (backlundCircleEnvelope_circleIntegrable hT)
    (backlundRightReducedEnvelope_circleIntegrable hT)
  intro s hs
  have hnorm : ‖s‖ = 33 / 25 := by
    simpa only [Metric.mem_sphere, dist_zero_right,
      abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25)] using hs
  unfold backlundRightReducedEnvelope
  split_ifs with hre
  · exact backlundCircleEnvelope_right_le hT hnorm.le hre
  · exact le_rfl

theorem positiveCount_backlund_right_reduced_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (Real.circleAverage (backlundRightReducedEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi +
      4 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  have h := div_le_div_of_nonneg_right
    (sub_le_sub_right (backlundCircleAverage_le_right_reduced hT)
      (Real.log ‖riemannZeta (backlundCenterPoint T)‖))
    (show 0 ≤ 2 * Real.log (44 / 25 : ℝ) by
      positivity)
  exact (positiveCount_backlund_gamma_paid_bound hT hr).trans_le
    (add_le_add (add_le_add (add_le_add h le_rfl) le_rfl) le_rfl)

#print axioms backlundRightReducedEnvelope_circleIntegrable
#print axioms backlundCircleAverage_le_right_reduced
#print axioms positiveCount_backlund_right_reduced_bound

end LiuWang.Proof.Campaign20260915.RosserCount
