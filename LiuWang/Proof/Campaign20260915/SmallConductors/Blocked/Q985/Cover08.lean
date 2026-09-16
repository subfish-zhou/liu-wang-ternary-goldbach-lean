import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985

theorem cover08 : ∀ i : Fin 32, 256 + i.val < 985 →
    Entry 985 generators (256 + i.val) (words.getD (256 + i.val) none) := by
  decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985
