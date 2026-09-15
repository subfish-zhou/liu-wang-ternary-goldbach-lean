import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Powers1269_1250

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q168

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, none, none, none, none, some (1, 2), none, some (1, 4), none, none, none, some (1, 8), none, some (1, 10), none, none, none, some (5, 11), none, some (5, 0), none, none, none, some (11, 12), none, some (5, 3), none, none, none, none, none, some (11, 9), none, none, none, some (11, 8), none, some (1, 7), none, none, none, some (5, 6), none, none, none, none, none, some (1, 12), none, some (1, 3), none, none, none, some (1, 15), none, some (11, 4), none, none, none, some (1, 5), none, some (5, 7), none, none, none, some (11, 11), none, some (5, 13), none, none, none, none, none, some (1, 14), none, none, none, some (11, 15), none, some (1, 9), none, none, none, some (5, 8), none, none, none, none, none, some (1, 11), none, some (1, 13), none, none, none, some (11, 1), none, some (11, 3), none, none, none, some (5, 2), none, some (5, 9), none, none, none, some (5, 5), none, some (11, 10), none, none, none, none, none, some (11, 0), none, none, none, some (5, 1), none, some (5, 14), none, none, none, some (5, 15), none, none, none, none, none, some (11, 5), none, some (5, 10), none, none, none, some (1, 6), none, some (11, 13), none, none, none, some (5, 12), none, some (11, 14), none, none, none, some (11, 2), none, some (5, 4), none, none, none, none, none, some (11, 7), none, none, none, some (11, 6)]
def generators : Fin 4 → ℕ := ![5, 11, 13, 17]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q168
