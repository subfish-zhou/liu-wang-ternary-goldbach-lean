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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q161

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (18, 0), some (1, 1), some (2, 0), some (1, 2), some (18, 1), none, some (13, 0), some (3, 0), some (18, 2), some (40, 3), some (2, 1), some (32, 1), none, some (1, 3), some (4, 0), some (10, 2), some (54, 0), some (6, 2), some (2, 2), none, some (62, 3), none, some (13, 1), some (5, 0), some (47, 1), some (3, 1), none, some (34, 0), some (18, 3), some (8, 1), some (26, 0), some (41, 2), some (19, 2), none, some (6, 0), some (25, 3), some (39, 2), some (19, 0), some (13, 2), some (11, 1), none, some (20, 3), some (11, 3), some (3, 2), none, some (33, 1), some (4, 1), none, some (48, 0), some (10, 3), some (41, 1), some (5, 3), some (54, 1), some (39, 1), none, some (6, 3), some (32, 0), some (55, 1), some (2, 3), some (62, 2), some (17, 1), none, some (8, 0), some (32, 3), some (25, 2), some (12, 3), some (20, 2), none, none, some (41, 0), some (39, 0), some (20, 1), some (33, 3), some (5, 1), some (12, 2), none, some (20, 0), some (4, 3), some (4, 2), some (9, 0), some (9, 1), some (9, 2), none, some (27, 0), some (31, 3), some (34, 1), some (9, 3), some (48, 2), some (54, 2), none, none, some (24, 0), some (27, 1), some (16, 0), some (26, 1), some (47, 2), none, some (41, 3), some (10, 0), some (62, 1), some (19, 3), some (27, 2), some (25, 1), none, some (48, 3), some (24, 3), some (6, 1), some (54, 3), some (12, 1), some (40, 2), none, some (34, 3), some (39, 3), none, some (47, 0), some (19, 1), some (24, 1), none, some (13, 3), some (11, 0), some (11, 2), some (33, 0), some (16, 1), some (5, 2), none, some (55, 0), some (17, 0), some (32, 2), some (47, 3), some (40, 1), some (33, 2), none, some (55, 3), some (3, 3), some (31, 2), some (16, 3), none, some (10, 1), none, some (62, 0), some (25, 0), some (24, 2), some (12, 0), some (34, 2), some (31, 1), none, some (27, 3), some (17, 3), some (48, 1), some (40, 0), some (55, 2), some (16, 2), none, some (8, 3), some (31, 0), some (17, 2), some (26, 3), some (8, 2), some (26, 2)]
def generators : Fin 2 → ℕ := ![3, 5]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q161
