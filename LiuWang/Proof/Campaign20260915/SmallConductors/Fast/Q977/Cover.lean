import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q977.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q977

theorem cover : SquareWordCover 977 generators words :=
  cover_of_fast_entries generators words (by decide +kernel)

theorem units : ∀ i, IsUnit (generators i : ZMod 977) :=
  generators_unit_of_coprime generators (by decide +kernel)

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q977
