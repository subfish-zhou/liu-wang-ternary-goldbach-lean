import LiuWang.Proof.Campaign20260915.RosserCount.BacklundExplicitCircle

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_cos_positive_integral_bound {r b c : ℝ}
    (hr : 0 ≤ r) (hc : c ∈ Set.Icc 0 (Real.pi / 2)) (hgc : 0 ≤ r * Real.cos c - b) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, max 0 (r * Real.cos θ - b)) ≤
      r * Real.sin c - b * c + (Real.pi / 2 - c) * (r * Real.cos c - b) := by
  have hi : Continuous (fun θ : ℝ => max 0 (r * Real.cos θ - b)) := by fun_prop
  have hfirst : (∫ θ in (0 : ℝ)..c, max 0 (r * Real.cos θ - b)) =
      r * Real.sin c - b * c := by
    have he : (∫ θ in (0 : ℝ)..c, max 0 (r * Real.cos θ - b)) =
        ∫ θ in (0 : ℝ)..c, r * Real.cos θ - b := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le hc.1] at hθ
      change max 0 (r * Real.cos θ - b) = r * Real.cos θ - b
      rw [max_eq_right]
      have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hθ.1
        (show c ≤ Real.pi by linarith [hc.2, Real.pi_pos]) hθ.2
      nlinarith [mul_le_mul_of_nonneg_left hcos hr]
    have hg : IntervalIntegrable (fun θ : ℝ => r * Real.cos θ) volume 0 c :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    rw [he, intervalIntegral.integral_sub hg
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      integral_cos, intervalIntegral.integral_const]
    simp only [Real.sin_zero, sub_zero, smul_eq_mul]
    ring
  have hsecond : (∫ θ in c..Real.pi / 2, max 0 (r * Real.cos θ - b)) ≤
      (Real.pi / 2 - c) * (r * Real.cos c - b) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hc.2 (hi.intervalIntegrable _ _)
      (intervalIntegrable_const (c := r * Real.cos c - b)) (fun θ hθ => by
        apply max_le hgc
        have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hc.1
          (show θ ≤ Real.pi by linarith [hθ.2, Real.pi_pos]) hθ.1
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left hcos hr) b)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable 0 c) (hi.intervalIntegrable c (Real.pi / 2)), hfirst]
  exact add_le_add le_rfl hsecond

def backlundLeftCoefficient (θ : ℝ) : ℝ :=
  (max 0 (-1 / 4 - (33 / 25 : ℝ) * Real.cos θ) +
    max 0 (-5 / 4 - (33 / 25 : ℝ) * Real.cos θ)) / 2

theorem backlundLeftCoefficient_continuous : Continuous backlundLeftCoefficient := by
  unfold backlundLeftCoefficient
  fun_prop

theorem backlund_left_coefficient_reflect :
    (∫ θ in Real.pi / 2..Real.pi, backlundLeftCoefficient θ) =
      ((∫ θ in (0 : ℝ)..Real.pi / 2, max 0 ((33 / 25 : ℝ) * Real.cos θ - 1 / 4)) +
        (∫ θ in (0 : ℝ)..Real.pi / 2, max 0 ((33 / 25 : ℝ) * Real.cos θ - 5 / 4))) / 2 := by
  have h := intervalIntegral.integral_comp_sub_left backlundLeftCoefficient
    (a := 0) (b := Real.pi / 2) Real.pi
  rw [sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at h
  rw [← h]
  have he (θ : ℝ) : backlundLeftCoefficient (Real.pi - θ) =
      (max 0 ((33 / 25 : ℝ) * Real.cos θ - 1 / 4) +
        max 0 ((33 / 25 : ℝ) * Real.cos θ - 5 / 4)) / 2 := by
    unfold backlundLeftCoefficient
    rw [Real.cos_pi_sub]
    congr 2 <;> congr 1 <;> ring
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add]
  · exact (by fun_prop : Continuous
      (fun θ : ℝ => max 0 ((33 / 25 : ℝ) * Real.cos θ - 1 / 4))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous
      (fun θ : ℝ => max 0 ((33 / 25 : ℝ) * Real.cos θ - 5 / 4))).intervalIntegrable _ _

#print axioms backlund_cos_positive_integral_bound
#print axioms backlundLeftCoefficient_continuous
#print axioms backlund_left_coefficient_reflect

end LiuWang.Proof.Campaign20260915.RosserCount
