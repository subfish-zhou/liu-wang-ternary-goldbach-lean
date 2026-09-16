import LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.SpectralReserves

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.PrincipalPsi.Quantitative

namespace LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

theorem selected_count_remainder_le_saddle {L : ℝ} (hL : 5000 ≤ L) :
    0.137 * Real.log (spectralCutoff L) +
      0.443 * Real.log (Real.log (spectralCutoff L)) + 1.588 ≤ saddle L := by
  have hs := saddle_ge_sixteen hL
  have hr0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr1 : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hu0 : 0 < saddle L / Real.sqrt 2 := div_pos (by linarith) hr0
  have hu : saddle L / Real.sqrt 2 ≤ saddle L := by
    apply (div_le_iff₀ hr0).mpr
    nlinarith
  rw [log_spectralCutoff]
  linarith [Real.log_le_sub_one_of_pos hu0]

theorem selected_boundary_reserve {L : ℝ} (hL : 5000 ≤ L) :
    4 * (0.137 * Real.log (spectralCutoff L) +
      0.443 * Real.log (Real.log (spectralCutoff L)) + 1.588) *
      rsPhi 1 L (spectralCutoff L) ≤
        (3 / 10 : ℝ) * saddle L ^ 2 * Real.exp (-2 * saddle L) := by
  have hs := saddle_ge_sixteen hL
  have hK0 : 0 < spectralCutoff L := Real.exp_pos _
  have hphi0 : 0 ≤ rsPhi 1 L (spectralCutoff L) := by unfold rsPhi; positivity
  have hphi : rsPhi 1 L (spectralCutoff L) ≤ Real.exp (-2 * saddle L) := by
    have h := phi_one_peak (by linarith : 0 ≤ L)
      (div_pos (by linarith : 0 < saddle L)
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
    have hr1 : 1 ≤ Real.sqrt (2 : ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    exact h.trans (Real.exp_le_exp.mpr (by nlinarith))
  calc
    _ ≤ (4 * saddle L) * rsPhi 1 L (spectralCutoff L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (selected_count_remainder_le_saddle hL) (by norm_num)) hphi0
    _ ≤ (4 * saddle L) * Real.exp (-2 * saddle L) :=
      mul_le_mul_of_nonneg_left hphi (by linarith)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith

theorem selected_spectral_budget {L : ℝ} (hL : 5000 ≤ L) :
    Real.exp (-L / 2) * (∑' p, rsZeroMoment 1 0 p) +
      (∑ p ∈ xiWindow 0 (spectralCutoff L), rsHighTerm rsA 1 L p) +
      4 * (0.137 * Real.log (spectralCutoff L) +
        0.443 * Real.log (Real.log (spectralCutoff L)) + 1.588) *
          rsPhi 1 L (spectralCutoff L) +
      2 * (rsQ (spectralCutoff L) * ∫ t in Ioi (spectralCutoff L),
        rsPhi 1 L t * Real.log (t / (2 * Real.pi))) ≤
          (smoothingStep L / 2) ^ (1 + 1 : ℕ) := by
  have hlow := weighted_first_moment_budget hL
  have hmid := actual_middle_spectrum_budget hL
  have hboundary := selected_boundary_reserve hL
  have htotal := integral_budget_reserve hL
  linarith

#print axioms selected_count_remainder_le_saddle
#print axioms selected_boundary_reserve
#print axioms selected_spectral_budget

end LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail
