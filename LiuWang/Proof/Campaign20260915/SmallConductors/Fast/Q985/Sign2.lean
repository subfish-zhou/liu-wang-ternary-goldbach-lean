import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q985.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q985

theorem certificate2 : VerifiedScan.Weighted 985 (squareValues words ![false, true]) 985 19 (10117 / 10000) := by
  unfold VerifiedScan.Weighted
  constructor <;> decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q985
