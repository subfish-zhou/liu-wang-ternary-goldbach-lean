import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q132

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, some (1, 2), none, none, none, none, none, some (1, 4), none, none, none, some (7, 5), none, some (19, 2), none, none, none, some (5, 7), none, some (5, 0), none, none, none, some (13, 5), none, some (5, 6), none, none, none, some (1, 3), none, some (13, 0), none, none, none, some (5, 5), none, some (5, 2), none, none, none, some (19, 7), none, some (7, 0), none, none, none, some (13, 1), none, none, none, none, none, some (1, 7), none, some (5, 4), none, none, none, some (1, 5), none, some (13, 6), none, none, none, some (13, 7), none, some (19, 4), none, none, none, none, none, some (7, 2), none, none, none, some (5, 3), none, some (13, 4), none, none, none, some (19, 1), none, some (1, 6), none, none, none, some (19, 3), none, some (19, 0), none, none, none, some (19, 5), none, some (7, 6), none, none, none, some (13, 3), none, some (7, 4), none, none, none, some (7, 1), none, some (19, 6), none, none, none, some (7, 7), none, none, none, none, none, some (5, 1), none, some (13, 2), none, none, none, some (7, 3)]
def generators : Fin 3 → ℕ := ![5, 7, 13]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q132
