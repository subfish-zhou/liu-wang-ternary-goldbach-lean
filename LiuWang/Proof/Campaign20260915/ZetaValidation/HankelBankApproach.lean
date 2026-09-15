import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelTiltedContour

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsHankelArcBetween_continuous (s : ℂ) (m : ℕ) {u : ℝ} (hu : u < 0) (a : ℝ) :
    Continuous (fun b : ℝ => rsHankelArcBetween s m u a b) := by
  have hc : Continuous (fun θ : ℝ => rsHankelLift s m (u + θ * I)) :=
    (rsHankelLift_joint_continuous m hu).comp
      (show Continuous (fun θ : ℝ => (s, θ)) by fun_prop)
  exact (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) a).const_mul I

theorem rsHankelRay_continuousOn_sector {m : ℕ} (hm : 0 < m) (s : ℂ) {u : ℝ} (hu : u < 0)
    {a b : ℝ} (hθ : ∀ θ ∈ uIcc a b, Real.sin θ ≤ -(1 / 2)) :
    ContinuousOn (rsHankelRay s m u) (uIcc a b) := by
  have hc := (continuous_const (y := rsHankelRay s m u a)).sub
    (rsHankelArcBetween_continuous s m hu a)
  apply hc.continuousOn.congr
  intro θ ht
  have h := rsHankelRay_rotation hm s u (a := a) (b := θ)
    (fun x hx => hθ x (uIcc_subset_uIcc_left ht hx))
  dsimp only [Pi.sub_apply]
  linear_combination -h

theorem rsHankelRightBank_integral_approach {m : ℕ} (hm : 0 < m) (s : ℂ) {u : ℝ} (hu : u < 0) :
    Tendsto (fun θ : ℝ =>
      ∫ x : ℝ in Ioi u, exp (x + θ * I) * rsHankelKernel s m (exp (x + θ * I)))
      (𝓝[Ioc (-(Real.pi / 2)) (-(Real.pi / 4))] (-(Real.pi / 2)))
      (𝓝 (∫ y : ℝ in Ioi (Real.exp u), rsHankelRightBank s m y)) := by
  have hab : -(Real.pi / 2) ≤ -(Real.pi / 4) := by linarith [Real.pi_pos]
  have hc := rsHankelRay_continuousOn_sector hm s hu
    (a := -(Real.pi / 2)) (b := -(Real.pi / 4)) (fun θ hθ =>
      rsHankel_right_sector_sin (by simpa [uIcc_of_le hab] using hθ))
  rw [uIcc_of_le hab] at hc
  have ht := (hc _ (left_mem_Icc.mpr hab)).mono Ioc_subset_Icc_self
  change Tendsto _ _ _ at ht
  rw [rsHankelRay_bottom_integral] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact rsHankelRay_actual s m u hθ.1 (by linarith [hθ.2, Real.pi_pos])

theorem rsHankelLeftBank_integral_approach {m : ℕ} (hm : 0 < m) (s : ℂ) {u : ℝ} (hu : u < 0) :
    Tendsto (fun θ : ℝ =>
      ∫ x : ℝ in Ioi u, exp (x + θ * I) * rsHankelKernel s m (exp (x + θ * I)))
      (𝓝[Ico (5 * Real.pi / 4) (3 * Real.pi / 2)] (3 * Real.pi / 2))
      (𝓝 (∫ y : ℝ in Ioi (Real.exp u), rsHankelLeftBank s m y)) := by
  have hab : 5 * Real.pi / 4 ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  have hc := rsHankelRay_continuousOn_sector hm s hu
    (a := 5 * Real.pi / 4) (b := 3 * Real.pi / 2) (fun θ hθ =>
      rsHankel_left_sector_sin (by simpa [uIcc_of_le hab] using hθ))
  rw [uIcc_of_le hab] at hc
  have ht := (hc _ (right_mem_Icc.mpr hab)).mono Ico_subset_Icc_self
  change Tendsto _ _ _ at ht
  rw [rsHankelRay_top_integral] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact rsHankelRay_actual s m u (by linarith [hθ.1, Real.pi_pos]) hθ.2

theorem rsHankelTiltedC1_actual (s : ℂ) (m : ℕ) (u : ℝ) :
    rsHankelTiltedC1 s m u =
      -(∫ x : ℝ in Ioi u, exp (x + (-(Real.pi / 4) : ℝ) * I) *
        rsHankelKernel s m (exp (x + (-(Real.pi / 4) : ℝ) * I))) +
      (∫ θ : ℝ in -(Real.pi / 4)..5 * Real.pi / 4,
        I * exp (u + θ * I) * rsHankelKernel s m (exp (u + θ * I))) +
      ∫ x : ℝ in Ioi u, exp (x + (5 * Real.pi / 4 : ℝ) * I) *
        rsHankelKernel s m (exp (x + (5 * Real.pi / 4 : ℝ) * I)) := by
  have hr := rsHankelRay_actual s m u (θ := -(Real.pi / 4))
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hl := rsHankelRay_actual s m u (θ := 5 * Real.pi / 4)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [rsHankelTiltedC1, hr, hl]
  congr 2
  rw [rsHankelArcBetween, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 4) ≤ 5 * Real.pi / 4)] at hθ
  dsimp only
  rw [rsHankelLift_actual s m
    (by simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero,
      zero_add]; linarith [hθ.1, Real.pi_pos])
    (by simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero,
      zero_add]; linarith [hθ.2, Real.pi_pos])]
  ring

end LiuWang.Proof.Campaign20260915.ZetaValidation
