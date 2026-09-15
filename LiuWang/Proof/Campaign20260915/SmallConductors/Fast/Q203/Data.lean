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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q203

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), some (24, 3), some (1, 3), none, some (2, 1), some (3, 0), some (48, 2), some (80, 1), some (2, 2), some (6, 3), none, some (44, 1), some (4, 0), some (34, 2), some (3, 1), some (33, 2), some (48, 3), none, some (15, 0), some (38, 0), some (2, 3), some (5, 0), some (12, 2), some (3, 2), none, none, some (59, 0), some (22, 2), some (4, 1), some (80, 3), some (34, 3), none, some (6, 0), some (27, 1), some (33, 3), some (11, 1), some (9, 2), some (31, 2), none, some (23, 1), some (15, 1), some (44, 3), some (38, 1), some (37, 2), some (4, 2), none, some (5, 1), some (73, 0), some (12, 3), some (16, 0), some (3, 3), some (17, 2), none, some (41, 0), none, some (40, 3), some (59, 1), some (30, 2), some (22, 3), none, some (8, 0), some (52, 0), some (15, 2), some (26, 0), some (19, 2), some (38, 2), none, some (48, 0), some (6, 1), some (69, 2), some (33, 0), some (5, 2), some (66, 2), none, some (22, 0), some (34, 1), some (9, 3), some (9, 0), some (31, 3), some (55, 3), none, some (12, 1), some (17, 0), none, some (30, 0), some (51, 2), some (59, 2), none, some (69, 0), some (66, 0), some (37, 3), some (31, 1), some (4, 3), some (10, 2), none, some (37, 1), some (10, 0), some (13, 2), some (73, 1), some (73, 3), some (24, 2), none, some (16, 1), some (80, 0), some (6, 2), some (44, 0), some (17, 3), some (27, 3), none, some (19, 1), some (41, 1), some (16, 3), none, some (11, 3), some (80, 2), none, some (27, 0), some (11, 0), some (30, 3), some (23, 0), some (44, 2), some (62, 3), none, some (51, 1), some (8, 1), some (23, 3), some (52, 1), some (40, 2), some (15, 3), none, some (26, 1), some (13, 1), some (19, 3), some (24, 1), some (38, 3), some (41, 3), none, some (34, 0), some (48, 1), some (55, 2), some (12, 0), none, some (69, 3), none, some (33, 1), some (31, 0), some (5, 3), some (37, 0), some (66, 3), some (73, 2), none, some (40, 1), some (22, 1), some (27, 2), some (19, 0), some (16, 2), some (11, 2), none, some (9, 1), some (55, 1), some (62, 2), some (51, 0), some (23, 2), some (20, 3), none, some (13, 0), some (24, 0), some (41, 2), some (17, 1), some (45, 3), none, none, some (30, 1), some (62, 1), some (51, 3), some (40, 0), some (59, 3), some (8, 3), none, some (55, 0), some (69, 1), some (20, 2), some (66, 1), some (52, 3), some (45, 2), none, some (62, 0), some (20, 1), some (8, 2), some (45, 1), some (10, 3), some (52, 2), none, some (20, 0), some (45, 0), some (26, 3), some (10, 1), some (26, 2), some (13, 3)]
def generators : Fin 2 → ℕ := ![2, 3]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q203
