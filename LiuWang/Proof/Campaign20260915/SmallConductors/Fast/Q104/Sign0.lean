import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104

def values0 : List ℤ := [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

theorem values0_eq : squareValues words ![false, false, false] = values0 := by rfl

theorem certificate0 : VerifiedScan.periodSum 104 (squareValues words ![false, false, false]) ≠ 0 := by
  rw [values0_eq]
  rw [periodSum_eq_list_sum (by decide : values0.length = 104)]
  decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104
