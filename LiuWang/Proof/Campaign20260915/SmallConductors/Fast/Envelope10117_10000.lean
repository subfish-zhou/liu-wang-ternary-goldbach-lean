import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.IntegerEnvelope

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Envelope10117_10000

def upper : List ℤ := [1000000000000, 1011700000000, 1023536890000, 1035512271613, 1047627765191, 1059885010044, 1072285664662, 1084831406938, 1097523934399, 1110364964432, 1123356234516, 1136499502459, 1149796546638]

theorem upper_bound : ∀ i : Fin 13, (1000000000000 : ℚ) *
    (10117 / 10000 : ℚ) ^ i.val ≤ (upper.getD i.val 0 : ℚ) :=
  by decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Envelope10117_10000
