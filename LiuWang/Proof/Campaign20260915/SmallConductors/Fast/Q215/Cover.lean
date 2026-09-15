import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q215.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q215

theorem cover : SquareWordCover 215 generators words :=
  cover_of_entries generators words (by decide +kernel) (by decide +kernel)

theorem units : ∀ i, IsUnit (generators i : ZMod 215) :=
  generators_unit_of_coprime generators (by decide +kernel)

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q215
