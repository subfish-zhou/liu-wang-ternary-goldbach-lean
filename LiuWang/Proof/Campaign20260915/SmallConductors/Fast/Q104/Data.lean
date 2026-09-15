import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (1, 2), none, some (7, 3), none, some (3, 0), none, some (1, 4), none, none, none, some (1, 3), none, some (11, 0), none, some (7, 4), none, some (5, 2), none, some (5, 6), none, some (5, 0), none, some (3, 1), none, some (3, 7), none, some (3, 3), none, some (1, 5), none, some (9, 1), none, some (7, 2), none, none, none, some (11, 5), none, some (7, 1), none, some (3, 2), none, some (11, 3), none, some (7, 0), none, some (11, 1), none, some (9, 7), none, some (1, 6), none, some (7, 5), none, some (9, 4), none, some (1, 7), none, some (5, 3), none, none, none, some (5, 4), none, some (5, 7), none, some (9, 3), none, some (9, 5), none, some (5, 1), none, some (7, 7), none, some (3, 6), none, some (9, 0), none, some (11, 4), none, some (11, 2), none, some (9, 6), none, some (3, 5), none, none, none, some (9, 2), none, some (7, 6), none, some (5, 5), none, some (3, 4), none, some (11, 7), none, some (11, 6)]
def generators : Fin 3 → ℕ := ![3, 5, 11]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104
