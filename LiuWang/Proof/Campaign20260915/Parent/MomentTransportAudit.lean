import LiuWang.Proof.Campaign20260915.ZetaMomentTransport.EndpointConsumers

/-! Actual high-zero input transported to the positive-height, multiplicity-bearing index.
The positive-height numerical budget and low-window certification are not proved here.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient
namespace LiuWang.Proof.Campaign20260915.Parent.MomentTransportAudit
open LiuWang.Proof.Campaign20260915.ZetaMomentTransport

theorem actual_high_sum_positive_transport {K L : ℝ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) {m : ℕ} (hm : 1 ≤ m) :
    (∑' p, rsHighTerm K m L p) ≤
      2 * ∑' p : RiemannXiDivisorZeroIndex,
        if K < (riemannXiDivisorZeroValue p).im then
          rsPhi m L (riemannXiDivisorZeroValue p).im else 0 :=
  rsHighTerm_sum_le_positive_xiPhi hK hL hm

#print axioms actual_high_sum_positive_transport
end LiuWang.Proof.Campaign20260915.Parent.MomentTransportAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.zetaWeight_conjugation
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.positiveZetaWeight_summable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.tsum_xi_eq_two_positive
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.tsum_xi_eq_two_positive_xi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.tsum_even_height
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.summable_closed
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.tsum_closed_eq_sum
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.positive_closed_transport
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.sum_closed_eq_two_positive
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.sum_height_window
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.tsum_closed_open
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.tsum_open_eq_two_positive
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.sum_closed_atom
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.sum_closed_strict_atom
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsZeroMoment_eq_two_positive
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsZeroMoment_zero_eq_two_inverse
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsHighTerm_eq_two_positive
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsPhi_xi_summable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsPhi_open_sum_eq_two
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsHighTerm_sum_le_two_positivePhi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsHighTerm_sum_le_of_positive_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsZeroMoment_closed_open_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsZeroMoment_low_window_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsZeroMoment_inverse_atom
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsZeroMoment_low_high_of_positiveValues
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsPsi_epsilon_of_positive_budgets
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.positiveHeightTail_eq_xi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsHighTerm_sum_le_positive_xiPhi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsZeroMoment_zero_eq_two_positive_xi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.tsum_boundary_eq_atom
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.tsum_closedTail_eq_open_add_atom
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.rsPhi_closedTail_eq_open_add_atom
