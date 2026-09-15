import LiuWang.Proof.Campaign20260915.Totient.RSOriginalIntegral

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Totient

def rsQ (K : ℝ) : ℝ :=
  1 / (2 * Real.pi) +
    (0.137 * Real.log K + 0.443) / (K * Real.log K * Real.log (K / (2 * Real.pi)))

theorem rsQ_le_original {K : ℝ} (hK : rsA ≤ K) : rsQ K ≤ 0.1592 := by
  have h1000 : 1000 ≤ K := rsA_ge_thousand.trans hK
  have hK0 : 0 < K := by linarith
  have hl : 999 / 100 ≤ Real.log K :=
    (Real.le_log_iff_exp_le hK0).mpr hK
  have hl0 : 0 < Real.log K := by linarith
  have hb := rs_log_two_pi_interval.2
  have hlog : 8 ≤ Real.log (K / (2 * Real.pi)) := by
    rw [Real.log_div hK0.ne' (by positivity)]
    linarith
  have hp : 1 / (2 * Real.pi) ≤ (0.15916 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [Real.pi_gt_d4]
  have hsmall : (0.137 * Real.log K + 0.443) / Real.log K ≤ 0.2 := by
    apply (div_le_iff₀ hl0).mpr
    linarith
  have hden : 8000 ≤ K * Real.log (K / (2 * Real.pi)) := by nlinarith
  have hrem : (0.137 * Real.log K + 0.443) /
      (K * Real.log K * Real.log (K / (2 * Real.pi))) ≤ (0.000025 : ℝ) := by
    calc
      _ = ((0.137 * Real.log K + 0.443) / Real.log K) /
          (K * Real.log (K / (2 * Real.pi))) := by rw [div_div]; ring
      _ ≤ 0.2 / (K * Real.log (K / (2 * Real.pi))) :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by linarith)
  unfold rsQ
  linarith

theorem rsQ_phi_integral_original {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L)
    (hupper : L < 1748 * (m : ℝ) ^ 2 / ((m : ℝ) + 0.123)) :
    rsQ rsA * (∫ t in Ioi rsA, rsPhi m L t * Real.log (t / (2 * Real.pi))) ≤
      (1.298 * (m : ℝ) + 0.1592) /
        ((1 - ((m : ℝ) + 0.123) * L / (1748 * (m : ℝ) ^ 2)) *
          (m : ℝ) ^ 2 * rsA ^ m * Real.exp (L / 175)) := by
  have hnon : 0 ≤ ∫ t in Ioi rsA, rsPhi m L t * Real.log (t / (2 * Real.pi)) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have hA : 2 * Real.pi ≤ t := by
      have h1000 := rsA_ge_thousand
      have hpi := Real.pi_lt_four
      change rsA < t at ht
      linarith
    have ht0 : 0 < t := (by positivity : (0 : ℝ) < 2 * Real.pi).trans_le hA
    apply mul_nonneg (by unfold rsPhi; positivity)
    apply Real.log_nonneg
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using hA)
  exact (mul_le_mul_of_nonneg_right (rsQ_le_original le_rfl) hnon).trans
    (rs_phi_integral_original hm hL hupper).2

#print axioms rsQ_le_original
#print axioms rsQ_phi_integral_original

end LiuWang.Proof.Campaign20260915.Totient
