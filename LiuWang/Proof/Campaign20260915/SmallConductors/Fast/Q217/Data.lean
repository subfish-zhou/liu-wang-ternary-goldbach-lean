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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q217

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (39, 0), some (1, 1), some (2, 0), some (1, 2), some (39, 1), none, some (15, 0), some (3, 0), some (39, 2), some (65, 3), some (2, 1), some (67, 1), none, some (1, 3), some (4, 0), some (27, 1), some (86, 0), some (48, 2), some (2, 2), none, some (55, 3), some (4, 3), some (15, 1), some (5, 0), some (9, 1), some (3, 1), none, some (29, 3), some (39, 3), none, some (30, 0), some (22, 2), some (32, 1), none, some (6, 0), some (53, 3), some (74, 2), some (16, 0), some (15, 2), some (23, 2), none, some (41, 3), some (25, 3), some (3, 2), some (30, 3), some (20, 2), some (4, 1), none, some (22, 0), some (74, 0), some (41, 1), some (86, 3), some (86, 1), some (46, 1), none, some (48, 3), some (46, 3), some (24, 2), some (2, 3), some (79, 1), none, none, some (8, 0), some (67, 3), some (10, 2), some (37, 0), some (23, 1), some (12, 2), none, some (34, 0), some (17, 0), some (13, 1), some (72, 3), some (5, 1), some (65, 2), none, some (27, 0), some (11, 3), some (4, 2), some (9, 0), some (29, 2), some (10, 1), none, some (27, 3), some (18, 3), some (25, 2), some (79, 3), some (65, 1), some (86, 2), none, some (8, 3), none, some (67, 2), some (23, 0), some (30, 1), some (72, 2), none, some (22, 3), some (10, 0), some (18, 2), some (65, 0), some (8, 2), some (18, 1), none, some (6, 3), some (18, 0), some (6, 1), some (58, 0), some (58, 1), some (58, 2), none, some (43, 0), some (74, 3), some (20, 1), some (58, 3), some (16, 1), some (37, 2), none, some (15, 3), some (11, 0), some (43, 1), some (23, 3), none, some (5, 2), none, some (36, 3), some (60, 0), some (32, 2), some (9, 3), some (43, 2), some (44, 2), none, some (48, 0), some (3, 3), some (29, 1), some (37, 3), some (34, 2), some (25, 1), none, some (20, 3), some (24, 0), some (17, 2), some (12, 0), some (72, 1), some (11, 1), none, some (13, 3), some (67, 0), some (22, 1), some (16, 3), some (55, 2), some (74, 1), none, none, some (32, 0), some (53, 2), some (5, 3), some (41, 2), some (30, 2), none, some (41, 0), some (46, 0), some (46, 2), some (79, 0), some (44, 1), some (60, 1), none, some (13, 0), some (32, 3), some (11, 2), some (51, 3), some (27, 2), some (79, 2), none, some (43, 3), some (24, 3), some (55, 1), some (44, 3), some (6, 2), some (53, 1), none, some (20, 0), some (60, 3), some (48, 1), none, some (36, 2), some (9, 2), none, some (29, 0), some (25, 0), some (8, 1), some (72, 0), some (13, 2), some (16, 2), none, some (34, 3), some (10, 3), some (36, 1), some (44, 0), some (37, 1), some (51, 2), none, some (55, 0), some (53, 0), some (60, 2), some (12, 3), some (51, 1), some (24, 1), none, some (36, 0), some (17, 3), some (34, 1), some (51, 0), some (12, 1), some (17, 1)]
def generators : Fin 2 → ℕ := ![3, 5]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q217
