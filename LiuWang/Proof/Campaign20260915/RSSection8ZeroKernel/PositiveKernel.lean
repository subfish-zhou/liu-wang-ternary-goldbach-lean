import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.OriginalKernel
import LiuWang.Proof.Campaign20260915.ZetaMomentTransport.EndpointConsumers
import LiuWang.Proof.Campaign20260915.Totient.RSCountLimit

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaMomentTransport
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

theorem zero_weight_tail_eq_two_positive {K : ℝ} (hK : rsA ≤ K) :
    (∑' p, rsHighTerm K 1 0 p) = 2 * ∑' p, rsPositivePhiTerm K 1 0 p := by
  have hK0 : 0 ≤ K := by linarith [rsA_ge_thousand]
  have h := rsPhi_open_sum_eq_two (m := 1) (by norm_num) (L := 0) (by norm_num) K
  rw [positiveHeightTail_eq_xi hK0
    (rsPhi_xi_summable (m := 1) (by norm_num) (L := 0) (by norm_num))] at h
  calc
    (∑' p, rsHighTerm K 1 0 p) =
        ∑' p : RiemannXiDivisorZeroIndex,
          if K < |(riemannXiDivisorZeroValue p).im| then
            rsPhi 1 0 |(riemannXiDivisorZeroValue p).im| else 0 := by
      apply tsum_congr
      intro p
      simp [rsHighTerm, rsPhi]
    _ = 2 * ∑' p, rsPositivePhiTerm K 1 0 p := by
      simpa only [rsPositivePhiTerm] using h

/-- The unweighted tail is exactly C02's actual positive-ordinate object. -/
theorem originalK_positive_cutoff {x K : ℝ} (hx : 1 ≤ x) (hK : rsA ≤ K) :
    originalK 1 x ≤
      (∑' p, closedMomentTerm rsA (Real.log x) p) +
        (∑' p, rsPositivePhiTerm rsA 1 0 p) / Real.sqrt x +
          x ^ (-(1 / (rsR * Real.log K))) * (∑' p, rsPositivePhiTerm rsA 1 0 p) +
            ∑' p, rsPositivePhiTerm K 1 0 p := by
  have h := originalK_variable_cutoff hx hK
  rw [zero_weight_tail_eq_two_positive (le_refl rsA),
    zero_weight_tail_eq_two_positive hK] at h
  exact h.trans_eq (by ring)

theorem originalK_one_eq_two_positive_inverse_square :
    originalK 1 1 =
      2 * ∑' p : RiemannXiDivisorZeroIndex,
        if 0 < (riemannXiDivisorZeroValue p).im then
          1 / (riemannXiDivisorZeroValue p).im ^ 2 else 0 := by
  rw [originalK_eq_moment 1 (by norm_num)]
  simpa only [Real.log_one] using
    rsZeroMoment_zero_eq_two_positive_xi (m := 1) (by norm_num)

#print axioms zero_weight_tail_eq_two_positive
#print axioms originalK_positive_cutoff
#print axioms originalK_one_eq_two_positive_inverse_square

end LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel
