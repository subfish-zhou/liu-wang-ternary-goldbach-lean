import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q105.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q105

def values4 : List ℤ := [0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 1, -1, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 1, 0, -1, 1, 0, -1, 0, 0, 1, -1, 0, 0, -1, 0, 1, 1, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 1, -1, 0, -1, -1, 0, 1, 0, 0, 1, -1, 0, 0, 1, 0, -1, 1, 0, -1, 0, 0, 1, 0, 0, -1, -1, 0, 0, 1, 0, 1, -1, 0, 0, 1, 0, -1, 0, 0, -1, 0, 0, 0, -1, 0, -1, -1]

theorem values4_eq : squareValues words ![false, false, true] = values4 := by rfl

theorem certificate4 : VerifiedScan.Weighted 105 (squareValues words ![false, false, true]) 105 6 (407 / 400) := by
  rw [values4_eq]
  apply weighted_of_list (t := 1) (B := 1000000000000)
  · decide +kernel
  · decide +kernel
  · norm_num
  · decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q105
