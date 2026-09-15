import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Imprimitive
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Envelope1269_1250

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q159

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (20, 1), none, some (22, 0), some (2, 1), none, some (13, 0), some (1, 2), none, some (38, 0), some (22, 1), none, some (4, 0), some (4, 2), none, some (14, 3), some (13, 1), none, some (1, 3), some (41, 1), none, some (5, 0), some (38, 1), none, some (44, 0), some (29, 2), none, some (23, 3), some (4, 1), none, some (4, 3), some (16, 1), none, some (14, 0), some (25, 2), none, some (26, 0), some (10, 1), none, some (19, 0), some (2, 2), none, some (29, 0), some (41, 2), none, some (7, 0), some (5, 1), none, some (23, 0), none, none, some (20, 3), some (44, 1), none, some (29, 3), some (11, 2), none, some (13, 3), some (7, 2), none, some (8, 0), some (35, 1), none, some (16, 3), some (8, 2), none, some (32, 0), some (50, 1), none, some (5, 3), some (14, 1), none, some (25, 3), some (22, 2), none, some (35, 3), some (26, 1), none, some (20, 0), some (11, 1), none, some (26, 3), some (19, 1), none, some (2, 3), some (14, 2), none, some (41, 0), some (29, 1), none, some (41, 3), some (23, 2), none, some (16, 0), some (7, 1), none, some (10, 0), some (17, 1), none, some (47, 3), some (23, 1), none, none, some (20, 2), none, some (32, 3), some (13, 2), none, some (35, 0), some (16, 2), none, some (50, 0), some (5, 2), none, some (11, 3), some (35, 2), none, some (11, 0), some (26, 2), none, some (7, 3), some (47, 1), none, some (38, 3), some (8, 1), none, some (17, 0), some (47, 2), none, some (10, 3), some (32, 2), none, some (8, 3), some (25, 1), none, some (44, 3), some (32, 1), none, some (47, 0), some (38, 2), none, some (50, 3), some (10, 2), none, some (25, 0), some (44, 2), none, some (19, 3), some (50, 2), none, some (22, 3), some (19, 2), none, some (17, 3), some (17, 2)]
def generators : Fin 2 → ℕ := ![2, 11]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q159
