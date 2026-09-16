import LiuWang.Proof.Campaign20260915.RosserCount.OriginalSharpCount
import LiuWang.Proof.Campaign20260915.Totient.RSTheorem27Transport
import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.UnweightedIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem rosser_positive_tail_theorem27 {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2) :
    (∑' p, rsPositivePhiTerm K m L p) <
      2 * rosserError K * rsPhi m L K +
      rsQ K * ∫ t in Ioi K, rsPhi m L t * Real.log (t / (2 * Real.pi)) :=
  rs_theorem27_from_sharp_count hK hL hm hupper
    (fun _ ht => rosserUpper_hasDerivAt (hK.trans ht))
    (fun _ ht => (positiveCount_original_rosser_bound (hK.trans ht)).le)

theorem rosser_positive_tail_corollary {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hupper : L ≤ ((m : ℝ) + 1) * rsR * Real.log K ^ 2) :
    (∑' p, rsPositivePhiTerm K m L p) <
      2 * rosserError K * rsPhi m L K +
      0.1592 * ∫ t in Ioi K, rsPhi m L t * Real.log (t / (2 * Real.pi)) := by
  have hn : 0 ≤ ∫ t in Ioi K, rsPhi m L t * Real.log (t / (2 * Real.pi)) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have ha := hK.trans ht.le
    exact mul_nonneg (rsPhi_pos m L (by linarith [rsA_ge_thousand])).le
      (rs_log_quot_pos ha).le
  exact (rosser_positive_tail_theorem27 hK hL hm hupper).trans_le
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (rsQ_le_original hK) hn))

theorem rosser_positive_inverse_square_tail {K : ℝ} (hK : rsA ≤ K) :
    (∑' p, rsPositivePhiTerm K 1 0 p) <
      2 * rosserError K / K ^ 2 +
      0.1592 * (1 + Real.log (K / (2 * Real.pi))) / K := by
  have h := rosser_positive_tail_corollary hK (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : 1 ≤ (1 : ℕ))
    (mul_nonneg (mul_nonneg (by norm_num) rsR_pos.le) (sq_nonneg _))
  rw [(unweighted_phi_integral hK).2] at h
  have he : rsPhi 1 0 K = 1 / K ^ 2 := by simp [rsPhi]
  rw [he] at h
  convert h using 1
  ring

#print axioms rosser_positive_tail_theorem27
#print axioms rosser_positive_tail_corollary
#print axioms rosser_positive_inverse_square_tail

end LiuWang.Proof.Campaign20260915.RosserCount
