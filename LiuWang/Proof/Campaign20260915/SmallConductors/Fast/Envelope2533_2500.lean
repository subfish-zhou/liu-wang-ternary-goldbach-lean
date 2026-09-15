import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.IntegerEnvelope

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Envelope2533_2500

def upper : List ℤ := [1000000000000, 1013200000000, 1026574240000, 1040125019968, 1053854670232, 1067765551879, 1081860057164, 1096140609918, 1110609665969, 1125269713560, 1140123273779, 1155172900993, 1170421183286]

theorem upper_bound : ∀ i : Fin 13, (1000000000000 : ℚ) *
    (2533 / 2500 : ℚ) ^ i.val ≤ (upper.getD i.val 0 : ℚ) :=
  by decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Envelope2533_2500
