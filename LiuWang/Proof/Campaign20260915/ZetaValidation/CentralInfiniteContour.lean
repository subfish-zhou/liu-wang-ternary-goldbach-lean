import LiuWang.Proof.Campaign20260915.ZetaValidation.CentralContourIdentity

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsCentralCircularTruncation_limit {m : ℕ} (hm : 0 < m) (s : ℂ) (R : ℝ) :
    Tendsto (rsCentralCircularTruncation s m R) atTop
      (𝓝 (rsHankelTiltedC1 s m (Real.log R))) := by
  have hcut : Tendsto rsCentralLogCutoff atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (show 0 < Real.sqrt 2 by positivity))
  have hr := intervalIntegral_tendsto_integral_Ioi (Real.log R)
    (rsHankelRay_integrable hm s (Real.log R)
      (rsHankel_right_sector_sin ⟨by linarith [Real.pi_pos], le_rfl⟩)) hcut
  have hl := intervalIntegral_tendsto_integral_Ioi (Real.log R)
    (rsHankelRay_integrable hm s (Real.log R)
      (rsHankel_left_sector_sin ⟨le_rfl, by linarith [Real.pi_pos]⟩)) hcut
  exact (hr.neg.add_const _).add hl

theorem rsCentralSourceTruncation_limit {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : s.re ≤ 1)
    {eta : ℝ} (hlo : (m : ℝ) < eta) (hhi : eta < m + 1) :
    Tendsto (rsCentralSourceTruncation s m eta) atTop (𝓝 (rsSourceC2 s eta m)) := by
  have he : 0 < eta := lt_of_le_of_lt (Nat.cast_nonneg m) hlo
  have hint : ∀ n : ℤ, eta ≠ n := by
    intro n hn
    have hh : (m : ℤ) < n ∧ n < (m : ℤ) + 1 := by
      exact_mod_cast (hn ▸ And.intro hlo hhi)
    omega
  have hcutR : Tendsto (fun T : ℝ => Real.sqrt 2 * T) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hcutL : Tendsto (fun T : ℝ => 1 + T / (rsC2Corner eta).im) atTop atTop :=
    tendsto_atTop_mono (fun T => by dsimp only [id_eq]; linarith)
      (tendsto_id.atTop_div_const (rsC2Corner_upper he).2)
  exact (intervalIntegral_tendsto_integral_Ioi (-eta / 2)
    (rsC2Right_integrable hm hs he hint) hcutR).neg.add
      (intervalIntegral_tendsto_integral_Ioi 0 (rsC2Left_integrable hm hs he) hcutL)

theorem rsHankelTiltedC1_eq_sourceC2 {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : s.re ≤ 1)
    {eta R : ℝ} (hlo : (m : ℝ) < eta) (hhi : eta < m + 1)
    (hR : (m : ℝ) < R) (hR' : R < m + 1) :
    rsHankelTiltedC1 s m (Real.log R) = rsSourceC2 s eta m := by
  have hA := rsCentralCircularTruncation_limit hm s R
  have hB := rsCentralSourceTruncation_limit hm hs hlo hhi
  have hH := rsC2_connectors_limit (eta := eta) hm hs
  have hsum := (hB.add hH.1).sub hH.2
  simp only [add_zero, sub_zero] at hsum
  apply tendsto_nhds_unique hA
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (rsCentral_finite_contour_identity s hlo hhi hR hR' hT).symm

theorem zeta_eq_source_sums_add_C2 {m : ℕ} (hm : 0 < m) {s : ℂ}
    (ht : 0 < s.im) (hs : s.re ≤ 1) {eta : ℝ}
    (hlo : (m : ℝ) < eta) (hhi : eta < m + 1) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
        (∑ k ∈ Finset.range m, (k + 1 : ℂ) ^ (s - 1)) +
      rsHankelPrefactor s * rsSourceC2 s eta m := by
  have hR : (m : ℝ) < (m : ℝ) + 1 / 2 := by linarith
  have hR' : (m : ℝ) + 1 / 2 < m + 1 := by linarith
  rw [zeta_eq_source_sums_add_expanded_hankel hm ht hR hR',
    rsHankelTiltedC1_eq_sourceC2 hm hs hlo hhi hR hR']

end LiuWang.Proof.Campaign20260915.ZetaValidation
