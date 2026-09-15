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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q187

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), some (8, 2), some (1, 3), some (49, 3), some (2, 1), some (3, 0), some (8, 3), none, some (2, 2), some (10, 1), some (21, 2), some (24, 0), some (4, 0), none, some (3, 1), some (35, 1), some (16, 2), some (40, 1), none, some (57, 2), some (2, 3), some (5, 0), some (20, 0), some (3, 2), some (21, 3), some (6, 3), some (24, 1), some (38, 2), some (4, 1), none, none, some (54, 1), some (6, 0), some (18, 2), some (15, 0), some (10, 3), some (16, 3), some (15, 3), some (63, 0), some (26, 1), none, some (24, 2), some (57, 3), some (60, 0), some (4, 2), some (7, 0), some (5, 1), none, some (20, 1), some (74, 0), some (3, 3), none, some (9, 2), some (35, 3), some (12, 2), some (46, 0), some (37, 0), some (43, 3), some (38, 3), some (40, 3), some (8, 0), some (63, 3), none, some (21, 0), none, some (16, 0), some (57, 0), some (52, 2), some (6, 1), some (27, 3), some (18, 3), some (5, 2), some (15, 1), none, some (20, 2), some (13, 3), some (32, 2), some (9, 0), some (30, 2), some (38, 1), some (63, 1), none, some (52, 0), some (18, 1), none, some (32, 0), some (24, 3), some (23, 2), some (29, 2), some (29, 0), some (60, 1), some (60, 3), some (4, 3), some (49, 2), some (7, 1), none, some (10, 0), some (12, 1), none, some (35, 0), some (40, 0), some (54, 3), some (74, 1), some (7, 3), some (6, 2), some (19, 3), none, some (54, 0), some (9, 3), some (10, 2), some (15, 2), some (26, 0), some (12, 3), some (30, 1), some (46, 1), none, some (37, 1), none, some (35, 2), some (23, 1), some (43, 2), some (40, 2), some (63, 2), some (49, 1), some (8, 1), some (26, 3), some (27, 2), some (74, 3), none, some (13, 2), some (21, 1), some (38, 0), none, some (18, 0), some (16, 1), some (71, 3), some (57, 1), some (60, 2), some (52, 3), none, some (12, 0), some (43, 1), some (54, 2), some (7, 2), some (19, 2), some (27, 1), some (5, 3), some (13, 1), some (30, 0), none, none, some (23, 0), some (20, 3), some (49, 0), some (26, 2), some (74, 2), some (32, 3), some (19, 1), some (9, 1), some (71, 2), some (30, 3), none, some (43, 0), some (46, 3), some (27, 0), some (13, 0), none, some (71, 1), some (52, 1), some (37, 3), some (19, 0), some (41, 3), none, some (46, 2), some (32, 1), some (71, 0), some (37, 2), some (41, 2), some (23, 3), some (41, 1), some (29, 3), some (41, 0), some (29, 1)]
def generators : Fin 2 → ℕ := ![2, 3]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q187
