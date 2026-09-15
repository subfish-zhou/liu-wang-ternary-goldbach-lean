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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q237

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (11, 1), none, some (1, 2), some (2, 1), none, some (22, 0), some (19, 1), none, some (31, 0), some (1, 3), none, some (4, 0), some (17, 3), none, some (16, 0), some (22, 1), none, some (38, 0), some (29, 1), none, some (5, 0), some (31, 1), none, some (2, 2), some (16, 3), none, some (49, 0), some (4, 1), none, some (34, 2), some (11, 3), none, some (28, 2), some (16, 1), none, some (35, 0), some (67, 3), none, some (35, 2), some (38, 1), none, some (58, 0), some (76, 3), none, some (7, 0), some (5, 1), none, some (17, 0), some (43, 3), none, some (23, 0), some (2, 3), none, some (32, 2), some (23, 3), none, some (40, 2), some (49, 1), none, some (8, 0), some (25, 1), none, some (64, 0), some (34, 3), none, some (22, 2), some (38, 3), none, some (28, 0), some (28, 3), none, some (32, 0), some (19, 3), none, none, some (35, 1), none, some (55, 2), some (70, 1), none, some (58, 2), some (35, 3), none, some (76, 0), some (20, 1), none, some (31, 2), some (58, 1), none, some (73, 2), some (61, 1), none, some (52, 0), some (7, 1), none, some (10, 0), some (13, 1), none, some (37, 2), some (17, 1), none, some (7, 2), some (70, 3), none, some (25, 2), some (23, 1), none, some (4, 2), some (5, 3), none, some (73, 0), some (32, 3), none, some (46, 2), some (40, 1), none, some (11, 0), some (40, 3), none, some (19, 0), some (55, 1), none, some (17, 2), some (8, 1), none, some (29, 0), some (37, 1), none, some (16, 2), some (64, 1), none, some (11, 2), some (14, 3), none, some (67, 2), some (22, 3), none, some (76, 2), some (43, 1), none, some (43, 2), some (28, 1), none, some (23, 2), some (20, 3), none, some (25, 0), some (32, 1), none, some (38, 2), some (14, 1), none, some (19, 2), none, none, some (70, 0), some (29, 3), none, some (20, 0), some (55, 3), none, some (61, 0), some (26, 1), none, some (13, 0), some (58, 3), none, some (70, 2), some (52, 3), none, some (5, 2), some (76, 1), none, some (40, 0), some (34, 1), none, some (55, 0), some (31, 3), none, some (37, 0), some (8, 3), none, some (14, 2), some (73, 3), none, some (43, 0), some (61, 3), none, some (20, 2), some (52, 1), none, some (14, 0), some (49, 3), none, some (29, 2), some (10, 1), none, some (26, 0), some (46, 1), none, some (52, 2), some (37, 3), none, some (34, 0), some (67, 1), none, some (8, 2), some (7, 3), none, some (61, 2), some (10, 3), none, some (49, 2), some (25, 3), none, some (46, 0), some (26, 3), none, some (67, 0), some (4, 3), none, some (10, 2), some (64, 3), none, some (26, 2), some (73, 1), none, some (64, 2), some (13, 3), none, some (13, 2), some (46, 3)]
def generators : Fin 2 → ℕ := ![2, 7]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q237
