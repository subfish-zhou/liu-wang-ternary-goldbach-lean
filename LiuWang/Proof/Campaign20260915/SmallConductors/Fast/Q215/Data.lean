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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q215

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (18, 1), some (2, 0), none, some (36, 0), some (81, 1), some (2, 1), some (3, 0), none, some (21, 0), some (36, 1), some (1, 2), some (33, 0), none, some (4, 0), some (27, 2), some (3, 1), some (3, 3), none, some (51, 0), some (21, 1), some (31, 2), some (57, 0), none, some (1, 3), some (11, 1), some (33, 1), some (47, 3), none, some (26, 0), some (4, 1), some (52, 1), some (27, 3), none, some (6, 0), some (56, 1), some (6, 2), some (18, 3), none, some (16, 0), some (51, 1), none, some (42, 0), none, some (31, 3), some (13, 2), some (57, 1), some (7, 0), none, some (56, 3), some (2, 2), some (76, 2), some (22, 0), none, some (66, 0), some (22, 2), some (51, 2), some (47, 0), none, some (41, 3), some (26, 1), some (28, 1), some (8, 0), none, some (61, 0), some (38, 2), some (11, 2), some (42, 3), none, some (21, 3), some (6, 1), some (12, 1), some (17, 0), none, some (6, 3), some (19, 1), some (36, 2), some (37, 0), none, some (9, 0), some (16, 1), some (66, 2), some (27, 0), none, none, some (28, 2), some (42, 1), some (12, 3), none, some (81, 3), some (62, 2), some (38, 1), some (13, 3), none, some (71, 0), some (57, 2), some (7, 1), some (23, 0), none, some (31, 0), some (17, 2), some (16, 2), some (2, 3), none, some (76, 3), some (52, 2), some (22, 1), some (18, 0), none, some (81, 0), some (66, 1), some (32, 1), some (22, 3), none, some (51, 3), some (3, 2), some (47, 1), some (37, 3), none, some (11, 0), some (47, 2), some (13, 1), some (52, 0), none, some (56, 0), some (18, 2), some (8, 1), none, none, some (71, 3), some (61, 1), some (56, 2), some (38, 3), none, some (11, 3), some (41, 1), some (41, 2), some (28, 0), none, some (19, 3), some (42, 2), some (21, 2), some (12, 0), none, some (19, 0), some (46, 1), some (17, 1), some (33, 3), none, some (14, 3), some (12, 2), some (81, 2), some (38, 0), none, some (36, 3), some (76, 1), some (37, 1), some (8, 3), none, some (26, 3), some (9, 1), some (62, 1), some (32, 0), none, some (66, 3), some (37, 2), some (27, 1), some (13, 0), none, some (9, 3), none, some (71, 2), some (28, 3), none, some (41, 0), some (14, 1), some (19, 2), some (32, 3), none, some (46, 0), some (33, 2), some (14, 2), some (62, 3), none, some (76, 0), some (8, 2), some (26, 2), some (62, 0), none, some (46, 3), some (71, 1), some (9, 2), some (57, 3), none, some (14, 0), some (32, 2), some (23, 1), some (7, 3), none, some (4, 3), some (31, 1), some (46, 2), some (17, 3), none, some (16, 3), some (7, 2), some (4, 2), some (23, 3), none, some (61, 3), some (23, 2), some (61, 2), some (52, 3)]
def generators : Fin 2 → ℕ := ![2, 13]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q215
