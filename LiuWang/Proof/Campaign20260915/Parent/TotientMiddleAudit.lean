import LiuWang.Proof.Campaign20260915.Totient.ProductAudit

/-! Parent verification of the actual middle-range integer consumer.
This does not discharge the all-q totient input of AllArcsPaid.
-/
set_option autoImplicit false
set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.Parent.TotientMiddleAudit

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

theorem actual_integer_bound {q : ℕ} (hq : 3 ≤ q)
    (hlog : Real.log (q : ℝ) ≤ 1340) :
    (q : ℝ) / (q.totient : ℝ) ≤ nu q :=
  original_RS_of_log_le_1340 hq hlog

theorem actual_product_bound {x : ℝ} (hx : 286 ≤ x) (hhi : x ≤ 1420) :
    (prefixEuler ⌊x⌋₊ : ℝ) <
      Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 1 / (2 * Real.log x)) :=
  product_3_29_finite hx hhi

#print axioms actual_integer_bound
#print axioms actual_product_bound

end LiuWang.Proof.Campaign20260915.Parent.TotientMiddleAudit
