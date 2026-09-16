import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985

theorem cover17 : ∀ i : Fin 32, 544 + i.val < 985 →
    Entry 985 generators (544 + i.val) (words.getD (544 + i.val) none) := by
  decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985
