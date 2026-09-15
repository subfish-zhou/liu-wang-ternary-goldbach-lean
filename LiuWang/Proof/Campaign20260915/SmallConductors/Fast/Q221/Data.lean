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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q221

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), some (61, 3), some (1, 3), some (70, 3), some (2, 1), some (3, 0), some (31, 2), some (89, 3), some (2, 2), none, some (55, 2), some (38, 1), some (4, 0), none, some (3, 1), some (35, 1), some (31, 3), some (11, 1), some (9, 2), some (57, 2), some (2, 3), some (5, 0), none, some (3, 2), some (55, 3), some (53, 2), some (76, 0), some (22, 3), some (4, 1), some (46, 1), none, some (16, 0), some (6, 0), some (37, 3), some (70, 0), none, some (23, 2), some (36, 3), some (22, 0), some (37, 0), some (9, 3), some (38, 3), some (57, 3), some (24, 1), some (4, 2), some (7, 0), some (5, 1), none, none, some (40, 0), some (3, 3), some (87, 0), some (59, 2), some (35, 3), some (53, 3), some (19, 1), some (76, 1), some (48, 2), some (44, 2), some (11, 3), some (8, 0), none, some (27, 0), some (12, 1), none, some (50, 0), some (16, 1), some (14, 3), some (6, 1), some (7, 3), some (74, 2), some (5, 2), some (70, 1), some (31, 0), none, some (10, 2), some (23, 3), some (9, 0), some (72, 2), some (55, 1), some (22, 1), none, some (37, 1), some (23, 0), some (18, 2), some (57, 1), some (76, 2), none, some (29, 2), some (53, 1), some (48, 0), some (20, 2), some (4, 3), some (40, 3), some (7, 1), some (46, 3), some (10, 0), some (72, 0), none, some (18, 0), none, some (16, 2), some (40, 1), some (25, 2), some (6, 2), some (87, 3), some (87, 1), some (59, 1), some (59, 3), some (61, 2), some (70, 2), some (44, 1), some (89, 2), none, some (38, 0), none, some (35, 0), some (11, 0), some (48, 3), some (74, 1), some (44, 3), some (33, 3), some (22, 2), some (46, 0), some (8, 1), some (37, 2), none, some (36, 2), some (27, 1), some (38, 2), some (24, 0), some (29, 1), none, some (20, 1), some (50, 1), some (35, 2), some (19, 0), some (24, 3), some (11, 2), none, some (12, 0), some (25, 1), some (14, 2), some (7, 2), some (74, 3), some (61, 1), some (5, 3), some (89, 1), some (55, 0), none, some (31, 1), some (57, 0), none, some (53, 0), some (10, 3), some (40, 2), some (46, 2), some (36, 1), some (9, 1), some (8, 3), some (72, 3), some (87, 2), some (59, 0), some (63, 3), some (44, 0), none, none, some (14, 1), some (74, 0), some (33, 2), some (23, 1), some (27, 3), some (18, 3), some (19, 3), some (29, 0), some (20, 0), some (76, 3), some (24, 2), none, some (25, 0), some (29, 3), some (61, 0), some (89, 0), none, some (48, 1), some (33, 1), some (20, 3), some (36, 0), some (8, 2), some (50, 3), some (63, 2), none, some (14, 0), some (42, 3), some (27, 2), some (19, 2), some (10, 1), some (12, 3), some (72, 1), some (63, 1), none, some (33, 0), some (18, 1), some (50, 2), none, some (42, 2), some (16, 3), some (12, 2), some (63, 0), some (42, 1), some (25, 3), some (21, 3), some (6, 3), some (42, 0), some (21, 2), some (21, 1), some (21, 0)]
def generators : Fin 2 → ℕ := ![2, 3]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q221
