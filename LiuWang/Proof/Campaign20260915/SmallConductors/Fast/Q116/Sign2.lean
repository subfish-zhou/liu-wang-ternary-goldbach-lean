import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q116.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q116

def values2 : List ℤ := [0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1]

theorem values2_eq : squareValues words ![false, true] = values2 := by rfl

theorem certificate2 : VerifiedScan.Weighted 116 (squareValues words ![false, true]) 116 12 (407 / 400) := by
  rw [values2_eq]
  apply weighted_of_list (t := 1) (B := 1000000000000)
  · decide +kernel
  · decide +kernel
  · norm_num
  · decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q116
