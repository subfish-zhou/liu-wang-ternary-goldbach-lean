import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightIntegral
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundSemicircle

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlundCircleAverage_right_budget {T : ℝ} (hT : rsA ≤ T) :
    Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) ≤
      5471 / 20000 + (1 / Real.pi) *
        (∫ θ in Real.pi / 2..Real.pi,
          backlundExplicitEnvelope T (circleMap 0 (33 / 25 : ℝ) θ)) := by
  have hp : Real.pi / 2 ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := by
    rw [Set.uIcc_of_le (by positivity)]
    constructor <;> linarith [Real.pi_pos]
  have hp' : Real.pi ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := by
    rw [Set.uIcc_of_le (by positivity)]
    constructor <;> linarith [Real.pi_pos]
  have he := backlundCircleEnvelope_circleIntegrable hT
  have hright := he.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hp)
  have hleft := he.mono_set (Set.uIcc_subset_uIcc hp hp')
  have hx := (backlundExplicitEnvelope_circleIntegrable T).mono_set
    (Set.uIcc_subset_uIcc hp hp')
  have hprof := backlundRightProfile_intervalIntegrable
    (a := 0) (b := Real.pi / 2)
    ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩
  have hr : (∫ θ in (0 : ℝ)..Real.pi / 2,
      backlundCircleEnvelope T (circleMap 0 (33 / 25 : ℝ) θ)) ≤
        Real.pi * (5471 / 20000) := by
    apply (intervalIntegral.integral_mono_on (by positivity) hright hprof _).trans
      backlund_right_integral_bound
    intro θ hθ
    have hc := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have h := backlund_right_dirichlet_log_bound (T := T)
      (s := circleMap 0 (33 / 25 : ℝ) θ)
      (by rw [circleMap_zero_re]; positivity) (N := 16) (by norm_num)
    simpa only [backlundRightProfile, circleMap_zero_re, add_comm] using h
  have hl : (∫ θ in Real.pi / 2..Real.pi,
      backlundCircleEnvelope T (circleMap 0 (33 / 25 : ℝ) θ)) ≤
      ∫ θ in Real.pi / 2..Real.pi,
        backlundExplicitEnvelope T (circleMap 0 (33 / 25 : ℝ) θ) := by
    apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hleft hx
    intro θ _
    have hn : ‖circleMap 0 (33 / 25 : ℝ) θ‖ ≤ 33 / 25 := by
      rw [norm_circleMap_zero, abs_of_pos (by norm_num)]
    unfold backlundExplicitEnvelope
    split_ifs with hl hr
    · exact backlundCircleEnvelope_left_le hT hn hl
    · exact backlundCircleEnvelope_right_le hT hn hr
    · exact backlundCircleEnvelope_middle_le hT hn (le_of_not_ge hl) (le_of_not_ge hr)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hright hleft
  have hhalf := backlundEnvelope_half_circle_integral hT
  have hb : Real.pi * Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) ≤
      Real.pi * (5471 / 20000) +
        (∫ θ in Real.pi / 2..Real.pi,
          backlundExplicitEnvelope T (circleMap 0 (33 / 25 : ℝ) θ)) := by
    rw [← hhalf, ← hadd]
    exact add_le_add hr hl
  apply le_of_mul_le_mul_left (a := Real.pi) _ Real.pi_pos
  simpa [mul_add, ← mul_assoc, Real.pi_ne_zero] using hb

theorem positiveCount_backlund_right_paid_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (5471 / 20000 + (1 / Real.pi) *
        (∫ θ in Real.pi / 2..Real.pi,
          backlundExplicitEnvelope T (circleMap 0 (33 / 25 : ℝ) θ)) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi +
      4 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  have h := div_le_div_of_nonneg_right
    (sub_le_sub_right (backlundCircleAverage_right_budget hT)
      (Real.log ‖riemannZeta (backlundCenterPoint T)‖))
    (show 0 ≤ 2 * Real.log (44 / 25 : ℝ) by positivity)
  exact (positiveCount_backlund_gamma_paid_bound hT hr).trans_le
    (add_le_add (add_le_add (add_le_add h le_rfl) le_rfl) le_rfl)

#print axioms backlundCircleAverage_right_budget
#print axioms positiveCount_backlund_right_paid_bound

end LiuWang.Proof.Campaign20260915.RosserCount
