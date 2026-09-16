import LiuWang.Proof.Campaign20260915.Totient.RSCountAudit
import LiuWang.Proof.Campaign20260915.RosserCount.OriginalRemainder

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.RosserCount

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_original_theorem27 {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2)
    (hcount : ∀ t ∈ Ici K, |(positiveCount t : ℝ) - rosserMain t| < rosserError t) :
    (∑' p, rsPositivePhiTerm K m L p) <
      2 * rosserError K * rsPhi m L K +
      rsQ K * ∫ t in Ioi K, rsPhi m L t * Real.log (t / (2 * Real.pi)) :=
  rs_theorem27_from_sharp_count hK hL hm hupper
    (fun _ ht => rosserUpper_hasDerivAt (hK.trans ht))
    (fun t ht => (hcount t ht).le)

theorem rs_original_theorem27_corollary {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2)
    (hcount : ∀ t ∈ Ici K, |(positiveCount t : ℝ) - rosserMain t| < rosserError t) :
    (∑' p, rsPositivePhiTerm K m L p) <
      2 * rosserError K * rsPhi m L K +
      0.1592 * ∫ t in Ioi K, rsPhi m L t * Real.log (t / (2 * Real.pi)) := by
  have hn : 0 ≤ ∫ t in Ioi K, rsPhi m L t * Real.log (t / (2 * Real.pi)) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have ha := hK.trans ht.le
    exact mul_nonneg (rsPhi_pos m L (by linarith [rsA_ge_thousand])).le
      (rs_log_quot_pos ha).le
  exact (rs_original_theorem27 hK hL hm hupper hcount).trans_le
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (rsQ_le_original hK) hn))

#print axioms rs_original_theorem27
#print axioms rs_original_theorem27_corollary

end LiuWang.Proof.Campaign20260915.Totient
