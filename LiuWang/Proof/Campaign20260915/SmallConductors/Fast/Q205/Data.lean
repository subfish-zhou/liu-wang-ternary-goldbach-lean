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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q205

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), none, some (1, 3), some (37, 2), some (2, 1), some (3, 0), none, some (6, 3), some (2, 2), some (31, 2), some (37, 3), none, some (4, 0), some (22, 2), some (3, 1), some (57, 3), none, some (29, 0), some (12, 2), some (27, 1), some (2, 3), none, some (31, 3), some (3, 2), some (49, 2), some (52, 3), none, some (21, 0), some (4, 1), some (18, 1), some (22, 3), none, some (6, 0), some (11, 1), some (9, 2), some (52, 0), none, none, some (29, 1), some (42, 1), some (12, 3), none, some (54, 0), some (17, 2), some (4, 2), some (7, 0), none, some (16, 0), some (62, 2), some (39, 2), some (3, 3), none, some (49, 3), some (34, 1), some (19, 2), some (72, 0), none, some (26, 0), some (21, 1), some (29, 2), some (8, 0), none, some (36, 0), some (47, 2), some (44, 2), some (27, 3), none, some (54, 3), some (6, 1), some (37, 1), some (22, 0), none, some (9, 3), some (31, 1), some (52, 1), some (67, 3), none, some (9, 0), none, some (12, 1), some (17, 0), none, some (39, 0), some (49, 1), some (24, 2), some (7, 3), none, some (44, 0), some (54, 1), some (21, 2), some (17, 3), none, some (4, 3), some (13, 2), some (7, 1), some (18, 3), none, some (16, 3), some (16, 1), some (62, 1), some (62, 3), none, some (39, 3), some (19, 1), some (6, 2), some (77, 3), none, some (11, 3), some (57, 2), some (47, 1), some (27, 0), none, some (19, 3), some (52, 2), some (72, 1), some (18, 0), none, some (11, 0), some (26, 1), none, some (42, 0), none, some (29, 3), some (24, 1), some (8, 1), some (42, 3), none, some (34, 0), some (36, 1), some (13, 1), some (47, 3), none, some (44, 3), some (27, 2), some (54, 2), some (37, 0), none, some (31, 0), some (67, 2), some (57, 1), some (12, 0), none, some (49, 0), some (7, 2), some (22, 1), some (72, 3), none, some (14, 3), some (18, 2), some (16, 2), some (62, 0), none, some (19, 0), some (77, 2), some (11, 2), some (47, 0), none, some (26, 3), some (9, 1), some (67, 1), none, none, some (24, 0), some (42, 2), some (17, 1), some (13, 0), none, some (34, 3), some (39, 1), some (77, 1), some (57, 0), none, some (24, 3), some (72, 2), some (14, 2), some (8, 3), none, some (59, 3), some (44, 1), some (26, 2), some (67, 0), none, some (21, 3), some (14, 1), some (34, 2), some (77, 0), none, some (36, 3), some (8, 2), some (59, 2), some (13, 3), none, some (14, 0), some (59, 1), some (36, 2), some (32, 3), none, some (59, 0), some (32, 2), some (32, 1), some (32, 0)]
def generators : Fin 2 → ℕ := ![2, 3]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q205
