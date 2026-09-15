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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q231

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (1, 2), none, none, some (2, 1), none, some (1, 3), none, none, some (25, 3), none, none, some (4, 0), some (1, 4), none, some (5, 3), some (2, 2), none, none, some (8, 7), none, some (5, 0), some (50, 2), none, none, some (19, 1), none, some (19, 5), some (4, 1), none, some (1, 5), none, none, some (31, 0), some (10, 2), none, some (2, 3), some (4, 4), none, some (13, 6), none, none, some (5, 6), some (29, 2), none, none, some (5, 1), none, some (50, 3), some (31, 7), none, none, none, none, some (17, 0), some (17, 2), none, some (26, 3), some (17, 4), none, some (8, 0), some (29, 1), none, some (23, 0), some (2, 4), none, none, some (23, 7), none, some (13, 3), some (31, 1), none, some (10, 3), none, none, some (17, 6), some (4, 2), none, some (4, 5), some (10, 4), none, some (1, 6), some (13, 7), none, none, some (8, 2), none, none, some (5, 7), none, some (29, 3), some (25, 1), none, some (8, 5), none, none, some (10, 0), some (13, 4), none, some (31, 5), some (23, 2), none, some (29, 6), some (13, 1), none, some (2, 6), none, none, none, some (26, 7), none, some (26, 5), some (17, 1), none, some (17, 3), none, none, none, some (25, 2), none, some (17, 5), some (5, 2), none, some (8, 6), some (8, 1), none, some (19, 0), some (19, 4), none, none, some (23, 1), none, some (2, 5), some (10, 7), none, some (31, 3), none, none, some (31, 6), none, none, some (19, 3), some (26, 2), none, some (29, 0), some (50, 1), none, some (23, 6), some (13, 2), none, none, some (19, 7), none, some (5, 5), some (17, 7), none, some (4, 3), none, none, some (25, 0), some (8, 4), none, some (10, 5), some (31, 4), none, some (13, 0), some (1, 7), none, some (26, 6), some (26, 4), none, none, none, none, some (8, 3), some (4, 7), none, some (29, 5), none, none, some (10, 6), some (31, 2), none, none, some (19, 2), none, some (50, 0), some (50, 7), none, some (19, 6), some (5, 4), none, none, some (26, 1), none, some (23, 5), some (10, 1), none, some (13, 5), none, none, some (4, 6), some (29, 4), none, some (23, 3), none, none, some (50, 6), some (29, 7), none, some (26, 0), some (23, 4), none, none, some (2, 7), none, none, some (25, 7), none, some (50, 5), none, none, some (25, 6), some (50, 4), none, some (25, 5), some (25, 4)]
def generators : Fin 3 → ℕ := ![2, 5, 17]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q231
