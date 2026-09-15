import LiuWang.Proof.Campaign20260915.Totient.ProductFinite
import LiuWang.Proof.Campaign20260915.Totient.ArithmeticCutoff
import LiuWang.Proof.Campaign20260915.Totient.Lemma15Geometry
import LiuWang.Proof.Campaign20260915.Totient.FiniteRange

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

namespace LiuWang.Proof.Campaign20260915.Totient

theorem original_RS_middle_two_point_five {q : ℕ}
    (hl : 255 ≤ Real.log (q : ℝ)) (hu : Real.log (q : ℝ) ≤ 1340) :
    (q : ℝ) / (q.totient : ℝ) <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log q) +
        2.5 / Real.log (Real.log q) := by
  let L := Real.log (q : ℝ)
  let y := 2 + 2 * Real.sqrt (1 + L)
  have hc := lemma15_middle_conditions hl hu
  change 288 ≤ L + y ∧ L < Chebyshev.theta (L + y) ∧
    0 ≤ y - 2 ∧ y - 2 ≤ (0.9 * L) / Real.log L ∧ L + y ≤ 1420 at hc
  have hq : 0 < q := by
    by_contra! hz
    have he : q = 0 := by omega
    simp only [he, Nat.cast_zero, Real.log_zero] at hl
    norm_num at hl
  have ht := theorem33_totient_cutoff hq (by linarith [hc.1]) hc.2.1
  have hp := product_3_29_finite (x := L + y - 2) (by linarith [hc.1])
    (by linarith [hc.2.2.2.2])
  exact (ht.trans_lt hp).trans_le (lemma15_scalar hl hc.2.2.1 hc.2.2.2.1)

theorem original_RS_of_log_le_1340 {q : ℕ} (hq : 3 ≤ q)
    (hu : Real.log (q : ℝ) ≤ 1340) :
    (q : ℝ) / (q.totient : ℝ) ≤ nu q := by
  by_cases hs : Real.log (q : ℝ) ≤ 294
  · exact original_RS_of_log_le_294 hq hs
  have hl : 255 ≤ Real.log (q : ℝ) := by linarith
  have h := original_RS_middle_two_point_five hl hu
  have hlog : 0 < Real.log (Real.log (q : ℝ)) :=
    Real.log_pos (by linarith)
  unfold nu
  exact h.le.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right (by norm_num : (2.5 : ℝ) ≤ 2.50637) hlog.le))

#print axioms product_3_29_finite
#print axioms theorem33_totient_cutoff
#print axioms original_RS_middle_two_point_five
#print axioms original_RS_of_log_le_1340

end LiuWang.Proof.Campaign20260915.Totient
