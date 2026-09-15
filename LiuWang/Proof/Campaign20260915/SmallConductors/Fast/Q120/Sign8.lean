import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q120.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q120

def values8 : List ℤ := [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]

theorem values8_eq : squareValues words ![false, false, false, true] = values8 := by rfl

theorem certificate8 : VerifiedScan.Weighted 120 (squareValues words ![false, false, false, true]) 120 8 (407 / 400) := by
  rw [values8_eq]
  apply weighted_of_list (t := 1) (B := 1000000000000)
  · decide +kernel
  · decide +kernel
  · norm_num
  · decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q120
