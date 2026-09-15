import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q120

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, none, none, some (1, 1), none, none, none, some (1, 2), none, some (1, 4), none, none, none, some (1, 8), none, some (7, 5), none, none, none, some (1, 6), none, none, none, none, none, some (7, 12), none, some (1, 14), none, none, none, none, none, some (7, 4), none, none, none, some (1, 7), none, some (7, 10), none, none, none, some (7, 6), none, some (7, 0), none, none, none, some (7, 3), none, none, none, none, none, some (7, 2), none, some (7, 11), none, none, none, none, none, some (1, 10), none, none, none, some (7, 9), none, some (7, 15), none, none, none, some (1, 3), none, some (7, 14), none, none, none, some (7, 13), none, none, none, none, none, some (7, 7), none, some (1, 5), none, none, none, none, none, some (1, 15), none, none, none, some (1, 12), none, some (7, 1), none, none, none, some (1, 13), none, some (1, 11), none, none, none, some (7, 8), none, none, none, none, none, some (1, 9)]
def generators : Fin 4 → ℕ := ![7, 11, 13, 17]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q120
