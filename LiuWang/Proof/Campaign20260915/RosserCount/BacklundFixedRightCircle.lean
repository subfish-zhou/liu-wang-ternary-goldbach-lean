import LiuWang.Proof.Campaign20260915.RosserCount.BacklundDirichletEnvelope

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Finset
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlundDirichletEnvelope_continuousOn {N : ℕ} (hN : 1 ≤ N) :
    ContinuousOn (backlundDirichletEnvelope N) (Ioi 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  intro x hx
  have hx1 : 1 < x := hx
  have hsum : Continuous (fun σ : ℝ => ∑ n ∈ range N, (n + 1 : ℝ) ^ (-σ)) := by
    apply continuous_finsetSum
    intro n _
    exact (Real.continuous_const_rpow (by positivity)).comp continuous_neg
  have htail : ContinuousAt (fun σ : ℝ => (N : ℝ) ^ (1 - σ) / (σ - 1)) x :=
    (((Real.continuous_const_rpow hNR.ne').comp (continuous_const.sub continuous_id)).continuousAt).div
      (continuous_id.sub continuous_const).continuousAt (by linarith)
  exact (hsum.continuousAt.add htail).continuousWithinAt

theorem backlundDirichletLog_clamped_continuous {N : ℕ} (hN : 1 ≤ N) :
    Continuous (fun s : ℂ =>
      Real.log (backlundDirichletEnvelope N (max (5 / 4) (s.re + 5 / 4)))) := by
  have hd : ContinuousOn (fun σ => Real.log (backlundDirichletEnvelope N σ)) (Ioi 1) :=
    (backlundDirichletEnvelope_continuousOn hN).log
      (fun σ hσ => (backlundDirichletEnvelope_pos hN hσ).ne')
  apply hd.comp_continuous (by fun_prop)
  intro s
  exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 5 / 4) (le_max_left _ _)

def backlundFixedRightEnvelope (N : ℕ) (T : ℝ) (s : ℂ) : ℝ :=
  if 0 ≤ s.re then
    Real.log (backlundDirichletEnvelope N (max (5 / 4) (s.re + 5 / 4)))
  else backlundExplicitEnvelope T s

theorem backlundFixedRightEnvelope_circleIntegrable {N : ℕ} (hN : 1 ≤ N) (T : ℝ) :
    CircleIntegrable (backlundFixedRightEnvelope N T) 0 (33 / 25 : ℝ) := by
  classical
  have hm : MeasurableSet {θ : ℝ | 0 ≤ (circleMap 0 (33 / 25 : ℝ) θ).re} :=
    measurableSet_le measurable_const (by fun_prop)
  have hc : IntervalIntegrable (fun θ : ℝ =>
      Real.log (backlundDirichletEnvelope N
        (max (5 / 4) ((circleMap 0 (33 / 25 : ℝ) θ).re + 5 / 4))))
      volume 0 (2 * Real.pi) :=
    ((backlundDirichletLog_clamped_continuous hN).comp (by fun_prop)).intervalIntegrable _ _
  have he := backlundExplicitEnvelope_circleIntegrable T
  constructor
  · exact Integrable.piecewise hm hc.1.integrableOn he.1.integrableOn
  · exact Integrable.piecewise hm hc.2.integrableOn he.2.integrableOn

theorem backlundCircleAverage_le_fixed_right {T : ℝ} (hT : rsA ≤ T)
    {N : ℕ} (hN : 1 ≤ N) :
    Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) ≤
      Real.circleAverage (backlundFixedRightEnvelope N T) 0 (33 / 25 : ℝ) := by
  apply Real.circleAverage_mono (backlundCircleEnvelope_circleIntegrable hT)
    (backlundFixedRightEnvelope_circleIntegrable hN T)
  intro s hs
  have hnorm : ‖s‖ = 33 / 25 := by
    simpa only [Metric.mem_sphere, dist_zero_right,
      abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25)] using hs
  unfold backlundFixedRightEnvelope
  split_ifs with hr
  · rw [max_eq_right (by linarith : 5 / 4 ≤ s.re + 5 / 4)]
    exact backlund_right_dirichlet_log_bound hr hN
  · unfold backlundExplicitEnvelope
    split_ifs with hl hm
    · exact backlundCircleEnvelope_left_le hT hnorm.le hl
    · exact backlundCircleEnvelope_right_le hT hnorm.le hm
    · exact backlundCircleEnvelope_middle_le hT hnorm.le (le_of_not_ge hl) (le_of_not_ge hm)

theorem positiveCount_backlund_fixed_right_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {N : ℕ} (hN : 1 ≤ N) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (Real.circleAverage (backlundFixedRightEnvelope N T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi +
      4 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  have h := div_le_div_of_nonneg_right
    (sub_le_sub_right (backlundCircleAverage_le_fixed_right hT hN)
      (Real.log ‖riemannZeta (backlundCenterPoint T)‖))
    (show 0 ≤ 2 * Real.log (44 / 25 : ℝ) by positivity)
  exact (positiveCount_backlund_gamma_paid_bound hT hr).trans_le
    (add_le_add (add_le_add (add_le_add h le_rfl) le_rfl) le_rfl)

#print axioms backlundDirichletEnvelope_continuousOn
#print axioms backlundDirichletLog_clamped_continuous
#print axioms backlundFixedRightEnvelope_circleIntegrable
#print axioms backlundCircleAverage_le_fixed_right
#print axioms positiveCount_backlund_fixed_right_bound

end LiuWang.Proof.Campaign20260915.RosserCount
