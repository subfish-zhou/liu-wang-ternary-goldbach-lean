import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q140.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q140

def values5 : List ℤ := [0, 1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, -1]

theorem values5_eq : squareValues words ![true, false, true] = values5 := by rfl

theorem certificate5 : VerifiedScan.Weighted 140 (squareValues words ![true, false, true]) 140 2 (1269 / 1250) := by
  rw [values5_eq]
  apply weighted_of_list (t := 1) (B := 1000000000000)
  · decide +kernel
  · decide +kernel
  · norm_num
  · decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q140
