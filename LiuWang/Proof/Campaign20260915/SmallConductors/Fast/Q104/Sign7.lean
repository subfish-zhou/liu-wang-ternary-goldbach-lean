import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104

def values7 : List ℤ := [0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1]

theorem values7_eq : squareValues words ![true, true, true] = values7 := by rfl

theorem certificate7 : VerifiedScan.Weighted 104 (squareValues words ![true, true, true]) 104 2 (407 / 400) := by
  rw [values7_eq]
  apply weighted_of_list (t := 1) (B := 1000000000000)
  · decide +kernel
  · decide +kernel
  · norm_num
  · decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104
