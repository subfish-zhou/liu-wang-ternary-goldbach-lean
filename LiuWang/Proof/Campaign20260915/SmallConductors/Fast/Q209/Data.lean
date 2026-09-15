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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q209

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), some (29, 0), some (1, 3), some (6, 3), some (2, 1), some (3, 0), some (29, 1), none, some (2, 2), some (23, 1), some (12, 2), some (29, 2), some (4, 0), some (43, 3), some (3, 1), none, some (58, 0), some (18, 1), none, some (21, 0), some (2, 3), some (5, 0), some (46, 0), some (3, 2), some (12, 3), some (47, 1), some (29, 3), some (17, 2), some (4, 1), none, some (9, 2), some (35, 3), some (6, 0), some (62, 2), none, some (23, 3), some (58, 1), some (31, 1), some (36, 0), some (36, 3), none, some (65, 0), some (21, 1), some (16, 0), some (4, 2), some (7, 0), some (5, 1), some (80, 1), some (46, 1), some (28, 2), some (3, 3), none, some (24, 2), none, some (39, 0), some (84, 2), some (58, 2), some (65, 3), some (17, 3), some (18, 3), some (8, 0), some (40, 1), none, some (42, 2), some (9, 3), some (21, 2), some (51, 2), some (69, 2), some (6, 1), some (16, 3), some (62, 3), some (5, 2), none, none, some (46, 2), some (12, 1), some (17, 0), some (9, 0), some (62, 0), some (32, 3), some (36, 1), some (7, 3), some (61, 2), some (47, 3), none, some (13, 2), some (65, 1), some (10, 2), some (42, 0), some (51, 0), some (16, 1), none, some (4, 3), some (27, 2), some (7, 1), none, some (10, 0), some (20, 3), some (27, 0), some (73, 2), some (73, 0), some (28, 1), some (28, 3), some (24, 1), some (6, 2), some (84, 1), none, some (23, 0), some (24, 3), some (43, 2), none, some (18, 0), some (39, 1), some (69, 1), some (84, 3), some (47, 0), some (58, 3), none, some (35, 2), some (31, 3), some (23, 2), some (31, 0), some (36, 2), some (61, 1), some (8, 1), some (13, 1), some (80, 0), some (14, 3), none, none, some (42, 3), some (65, 2), some (18, 2), some (40, 0), some (21, 3), some (39, 3), some (51, 3), some (16, 2), some (69, 3), none, some (12, 0), some (43, 1), some (32, 2), some (7, 2), some (47, 2), some (54, 3), some (5, 3), some (35, 1), none, some (80, 3), none, some (20, 2), some (46, 3), some (28, 0), some (24, 0), some (84, 0), some (17, 1), some (50, 3), some (9, 1), some (69, 0), some (62, 1), none, some (31, 2), some (32, 1), some (61, 0), some (13, 0), some (14, 2), none, some (61, 3), some (20, 1), some (39, 2), some (8, 3), none, some (43, 0), some (13, 3), some (54, 2), some (35, 0), some (80, 2), some (10, 3), some (14, 1), some (42, 1), some (50, 2), some (51, 1), none, some (32, 0), some (54, 1), none, some (20, 0), some (8, 2), some (50, 1), some (27, 3), some (40, 3), some (14, 0), some (25, 3), none, some (54, 0), some (10, 1), some (50, 0), some (40, 2), some (25, 2), some (27, 1), some (25, 1), some (73, 3), some (25, 0), some (73, 1)]
def generators : Fin 2 → ℕ := ![2, 3]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q209
