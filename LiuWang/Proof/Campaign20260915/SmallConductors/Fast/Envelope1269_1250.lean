import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.IntegerEnvelope

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Envelope1269_1250

def upper : List ℤ := [1000000000000, 1015200000000, 1030631040000, 1046296631808, 1062200340612, 1078345785789, 1094736641733, 1111376638688, 1128269563596, 1145419260962, 1162829633729, 1180504644162, 1198448314753]

theorem upper_bound : ∀ i : Fin 13, (1000000000000 : ℚ) *
    (1269 / 1250 : ℚ) ^ i.val ≤ (upper.getD i.val 0 : ℚ) :=
  by decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Envelope1269_1250
