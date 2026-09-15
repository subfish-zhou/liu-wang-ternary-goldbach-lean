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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q185

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), none, some (1, 3), some (8, 2), some (2, 1), some (3, 0), none, some (14, 0), some (2, 2), some (32, 1), some (8, 3), none, some (4, 0), some (29, 1), some (3, 1), some (53, 3), none, some (24, 0), some (14, 1), some (17, 1), some (2, 3), none, some (64, 0), some (3, 2), some (16, 2), some (23, 3), none, some (6, 3), some (4, 1), some (14, 2), some (53, 0), none, some (6, 0), none, some (69, 2), some (32, 3), none, some (39, 0), some (24, 1), some (22, 1), some (28, 0), none, some (34, 0), some (18, 2), some (4, 2), some (7, 0), none, some (29, 3), some (64, 1), some (54, 2), some (3, 3), none, some (16, 3), some (11, 1), some (9, 2), some (33, 3), none, some (39, 3), some (12, 2), some (24, 2), some (8, 0), none, some (14, 3), some (48, 2), some (53, 1), some (17, 3), none, some (16, 0), some (6, 1), some (44, 2), none, none, some (69, 3), some (38, 2), some (64, 2), some (28, 3), none, some (9, 0), some (39, 1), some (59, 2), some (48, 0), none, some (44, 0), some (69, 1), some (28, 1), some (13, 3), none, some (34, 3), some (34, 1), some (18, 1), some (18, 3), none, some (4, 3), some (54, 1), some (7, 1), some (32, 0), none, some (29, 0), some (53, 2), some (12, 1), some (17, 0), none, some (54, 3), some (23, 2), some (6, 2), some (7, 3), none, none, some (32, 2), some (38, 1), some (22, 0), none, some (9, 3), some (59, 1), some (29, 2), some (27, 3), none, some (11, 0), some (33, 2), some (39, 2), some (12, 3), none, some (24, 3), some (17, 2), some (8, 1), some (22, 3), none, some (19, 3), some (28, 2), some (23, 1), some (48, 3), none, some (69, 0), some (13, 2), some (34, 2), some (18, 0), none, some (54, 0), some (16, 1), some (33, 1), some (12, 0), none, some (44, 3), some (7, 2), none, some (38, 0), none, some (59, 0), some (27, 2), some (13, 1), some (38, 3), none, some (64, 3), some (22, 2), some (19, 2), some (23, 0), none, some (49, 3), some (9, 1), some (27, 1), some (33, 0), none, some (59, 3), some (19, 1), some (48, 1), some (13, 0), none, some (11, 3), some (44, 1), some (49, 2), some (27, 0), none, some (19, 0), some (49, 1), some (11, 2), some (43, 3), none, some (49, 0), some (43, 2), some (43, 1), some (43, 0)]
def generators : Fin 2 → ℕ := ![2, 3]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q185
