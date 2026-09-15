import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q123

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (8, 1), none, some (1, 2), some (2, 1), none, some (16, 0), some (19, 3), none, some (23, 2), some (1, 3), none, some (4, 0), some (16, 3), none, some (14, 2), some (16, 1), none, some (38, 2), some (14, 1), none, some (5, 0), some (23, 3), none, some (2, 2), some (13, 3), none, some (20, 0), some (4, 1), none, some (32, 2), some (8, 3), none, some (23, 0), some (14, 3), none, some (32, 0), none, none, some (17, 0), some (38, 3), none, some (13, 0), some (10, 3), none, some (7, 0), some (5, 1), none, some (5, 2), some (35, 3), none, some (17, 2), some (2, 3), none, some (26, 2), some (38, 1), none, some (26, 0), some (20, 1), none, some (8, 0), some (20, 3), none, some (19, 2), some (32, 3), none, some (16, 2), some (7, 3), none, some (14, 0), some (23, 1), none, some (13, 2), some (10, 1), none, some (8, 2), some (32, 1), none, none, some (29, 1), none, some (10, 2), some (17, 1), none, some (35, 2), some (29, 3), none, some (38, 0), some (13, 1), none, some (20, 2), some (11, 3), none, some (7, 2), some (7, 1), none, some (10, 0), some (4, 3), none, some (29, 0), some (5, 3), none, some (29, 2), some (19, 1), none, some (11, 2), some (17, 3), none, some (4, 2), some (35, 1), none, some (19, 0), some (26, 3), none, some (35, 0), some (11, 1), none, some (11, 0), some (26, 1)]
def generators : Fin 2 → ℕ := ![2, 7]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q123
