import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelRayRotation

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsHankelTiltedC1 (s : ℂ) (m : ℕ) (u : ℝ) : ℂ :=
  -rsHankelRay s m u (-(Real.pi / 4)) +
    rsHankelArcBetween s m u (-(Real.pi / 4)) (5 * Real.pi / 4) +
      rsHankelRay s m u (5 * Real.pi / 4)

theorem rsHankelArcBetween_add (s : ℂ) (m : ℕ) {u : ℝ} (hu : u < 0) (a b c : ℝ) :
    rsHankelArcBetween s m u a b + rsHankelArcBetween s m u b c =
      rsHankelArcBetween s m u a c := by
  have hc : Continuous (fun θ : ℝ => rsHankelLift s m (u + θ * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (rsHankelLift_analytic s m (by simpa)).continuousAt.comp (by fun_prop)
  simp only [rsHankelArcBetween, ← mul_add]
  rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a b)
    (hc.intervalIntegrable b c)]

theorem rsHankelRay_bottom_integral (s : ℂ) (m : ℕ) (u : ℝ) :
    rsHankelRay s m u (-(Real.pi / 2)) =
      ∫ y : ℝ in Ioi (Real.exp u), rsHankelRightBank s m y := by
  simp_rw [rsHankelRay, rsHankelLift_bottom]
  simpa only [real_smul, smul_eq_mul] using integral_comp_exp_Ioi (rsHankelRightBank s m) u

theorem rsHankelRay_top_integral (s : ℂ) (m : ℕ) (u : ℝ) :
    rsHankelRay s m u (3 * Real.pi / 2) =
      ∫ y : ℝ in Ioi (Real.exp u), rsHankelLeftBank s m y := by
  simp_rw [rsHankelRay, rsHankelLift_top]
  simpa only [real_smul, smul_eq_mul] using integral_comp_exp_Ioi (rsHankelLeftBank s m) u

theorem rsHankelC1_eq_tilted {m : ℕ} (hm : 0 < m) (s : ℂ) {u : ℝ} (hu : u < 0) :
    rsHankelC1 s m u = rsHankelTiltedC1 s m u := by
  have hr := rsHankelRay_rotation hm s u
    (a := -(Real.pi / 2)) (b := -(Real.pi / 4)) (fun θ hθ =>
      rsHankel_right_sector_sin (by
        simpa [uIcc_of_le (by linarith [Real.pi_pos] :
          -(Real.pi / 2) ≤ -(Real.pi / 4))] using hθ))
  have hl := rsHankelRay_rotation hm s u
    (a := 5 * Real.pi / 4) (b := 3 * Real.pi / 2) (fun θ hθ =>
      rsHankel_left_sector_sin (by
        simpa [uIcc_of_le (by linarith [Real.pi_pos] :
          5 * Real.pi / 4 ≤ 3 * Real.pi / 2)] using hθ))
  have h1 := rsHankelArcBetween_add s m hu (-(Real.pi / 2)) (-(Real.pi / 4)) (5 * Real.pi / 4)
  have h2 := rsHankelArcBetween_add s m hu (-(Real.pi / 2)) (5 * Real.pi / 4) (3 * Real.pi / 2)
  rw [rsHankelRay_bottom_integral] at hr
  rw [rsHankelRay_top_integral] at hl
  change rsHankelArcBetween s m u (-(Real.pi / 2)) (3 * Real.pi / 2) + _ - _ = _
  unfold rsHankelTiltedC1
  linear_combination -hr - hl - h1 - h2

theorem zeta_eq_sum_add_tilted_hankel {m : ℕ} (hm : 0 < m)
    {s : ℂ} (ht : 0 < s.im) {u : ℝ} (hu : u < 0) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      rsHankelPrefactor s * rsHankelTiltedC1 s m u := by
  rw [← rsHankelC1_eq_tilted hm s hu]
  exact zeta_eq_fixed_hankel_upper hm hu ht

theorem rsHankelTilted_tails_integrable {m : ℕ} (hm : 0 < m) (s : ℂ) (u : ℝ) :
    IntegrableOn (fun x : ℝ => exp (x + (-(Real.pi / 4) : ℝ) * I) *
      rsHankelKernel s m (exp (x + (-(Real.pi / 4) : ℝ) * I))) (Ioi u) ∧
    IntegrableOn (fun x : ℝ => exp (x + (5 * Real.pi / 4 : ℝ) * I) *
      rsHankelKernel s m (exp (x + (5 * Real.pi / 4 : ℝ) * I))) (Ioi u) := by
  have aux (θ : ℝ) (hlo : -(Real.pi / 2) < θ) (hhi : θ < 3 * Real.pi / 2)
      (hsin : Real.sin θ ≤ -(1 / 2)) :
      IntegrableOn (fun x : ℝ => exp (x + θ * I) *
        rsHankelKernel s m (exp (x + θ * I))) (Ioi u) := by
    apply (rsHankelRay_integrable hm s u hsin).congr_fun _ measurableSet_Ioi
    intro x _
    exact rsHankelLift_actual s m (by simpa using hlo) (by simpa using hhi)
  constructor
  · exact aux _ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      (rsHankel_right_sector_sin ⟨by linarith [Real.pi_pos], le_rfl⟩)
  · exact aux _ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      (rsHankel_left_sector_sin ⟨le_rfl, by linarith [Real.pi_pos]⟩)

end LiuWang.Proof.Campaign20260915.ZetaValidation
