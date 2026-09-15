import LiuWang.Proof.Campaign20260915.Totient.RSCountAudit
import LiuWang.Proof.Campaign20260915.ZetaMomentTransport.EndpointConsumers
import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.PositiveKernel

/-! Actual positive-height Abel chain and its full-spectrum consumer.
The sharp counting hypothesis is explicit and not proved by this transport.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set
namespace LiuWang.Proof.Campaign20260915.Parent.CountAbelAudit
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

theorem actual_high_sum_to_positive {K L : ℝ} (hK : rsA ≤ K)
    (hL : 0 ≤ L) {m : ℕ} (hm : 1 ≤ m) :
    (∑' p, rsHighTerm K m L p) ≤ 2 * ∑' p, rsPositivePhiTerm K m L p := by
  simpa only [rsPositivePhiTerm] using
    LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsHighTerm_sum_le_positive_xiPhi hK hL hm

theorem actual_high_tail_from_sharp_count {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2)
    {F E : ℝ → ℝ}
    (hderiv : ∀ t ∈ Ici K, HasDerivAt (fun u => F u + E u)
      (rsQ t * Real.log (t / (2 * Real.pi))) t)
    (hcount : ∀ t ∈ Ici K, |(positiveCount t : ℝ) - F t| ≤ E t) :
    (∑' p, rsHighTerm K m L p) <
      4 * E K * rsPhi m L K +
        2 * rsQ K * ∫ t in Ioi K, rsPhi m L t * Real.log (t / (2 * Real.pi)) := by
  have h := rs_theorem27_from_sharp_count hK hL hm hupper hderiv hcount
  have hh := (actual_high_sum_to_positive hK hL hm).trans_lt
    (mul_lt_mul_of_pos_left h (by norm_num : (0 : ℝ) < 2))
  linarith only [hh]

#print axioms actual_high_sum_to_positive
#print axioms actual_high_tail_from_sharp_count
end LiuWang.Proof.Campaign20260915.Parent.CountAbelAudit

#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_integral_weighted_step
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveCount_weighted_integral
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveCount_abel
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPhi_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPhiSlope_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPhi_pos
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPhi_le_power
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPhiSlope_nonpos
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPhi_antitoneOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveCount_phi_abel
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsQ_antitoneOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPositivePhiTerm_nonneg
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPositivePhiTerm_summable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveCount_coarse
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveCount_phi_tendsto
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveWindow_phi_tendsto
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_count_phi_intervalIntegrable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_count_phi_integral_tendsto
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_count_phi_integrableOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveCount_phi_abel_infinite
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveCount_majorant_finite
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveCount_two_remainders_finite
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positiveCount_two_remainders_infinite
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_log_quot_pos
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsQ_split
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsQ_pos
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsQ_strictAntiOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsQ_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_phi_log_integrableOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsQ_phi_density_integrableOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsQ_phi_density_strict
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_theorem27_from_sharp_count
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.zero_weight_tail_eq_two_positive
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.originalK_positive_cutoff
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.originalK_one_eq_two_positive_inverse_square
