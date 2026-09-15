import LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q101.Table

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q101

theorem certificate0 : VerifiedScan.periodSum 101 (squareValues words ![false]) ≠ 0 := by
  decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q101
