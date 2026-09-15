import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q105

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), none, none, none, some (2, 1), none, none, some (1, 2), none, some (1, 4), none, none, some (4, 0), some (8, 6), none, some (17, 7), none, none, some (1, 3), some (8, 1), none, none, some (1, 5), none, none, some (17, 2), none, some (16, 7), some (4, 1), none, some (8, 7), none, none, some (4, 3), some (1, 6), none, none, some (16, 5), none, some (8, 3), some (2, 2), none, some (16, 0), some (2, 6), none, none, none, none, some (2, 4), some (17, 1), none, none, none, none, some (17, 3), some (17, 5), none, some (4, 7), some (17, 6), none, some (8, 0), none, none, some (16, 3), some (16, 6), none, none, some (4, 2), none, some (16, 4), some (8, 2), none, some (1, 7), none, none, some (17, 0), none, none, some (17, 4), some (4, 6), none, none, some (16, 2), none, some (2, 3), some (8, 5), none, none, some (16, 1), none, some (2, 7), none, none, some (8, 4), none, none, none, some (4, 5), none, some (4, 4), some (2, 5)]
def generators : Fin 3 → ℕ := ![2, 11, 13]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q105
