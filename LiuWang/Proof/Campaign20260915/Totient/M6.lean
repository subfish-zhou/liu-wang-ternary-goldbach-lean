import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.Nu
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.Payment

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Totient

theorem third_sourceNu_eq_nu (x : ℝ) : sourceNu x = nu x := rfl

theorem third_sourceNu_monotoneOn : MonotoneOn sourceNu (Set.Ici 100000) :=
  nu_monotoneOn

theorem third_sourceNu_le_sixth {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sourceNu q ≤ sourceNu (sourceL N ^ 6) := by
  have hP : 100000 ≤ sourceP N := by linarith [sourceP_ge_ten_billion hN]
  have hq0 : 100000 ≤ (q : ℝ) := hP.trans hq
  exact third_sourceNu_monotoneOn hq0 (hq0.trans hq1) hq1

theorem equation_5_44_with_monotonicity_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    sourceM6 N q ≤ (6 / 1000000000 : ℝ) * (N : ℝ) / sourceL N :=
  M6Certificate.equation_5_44_paid hN hq hq1 htotient
    (third_sourceNu_le_sixth hN hq hq1)

end LiuWang.Proof.Campaign20260915.Totient
