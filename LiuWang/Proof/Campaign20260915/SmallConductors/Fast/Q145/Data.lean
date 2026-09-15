import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q145

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (33, 1), some (2, 0), none, some (21, 0), some (1, 2), some (2, 1), some (3, 0), none, some (23, 3), some (21, 1), some (8, 2), some (1, 3), none, some (4, 0), some (9, 1), some (3, 1), some (36, 3), none, some (33, 3), some (41, 2), some (13, 2), some (13, 0), none, some (8, 3), some (41, 1), some (2, 2), none, none, some (53, 3), some (4, 1), some (48, 2), some (18, 0), none, some (6, 0), some (31, 1), some (43, 2), some (26, 3), none, some (18, 3), some (21, 2), some (23, 1), some (41, 3), none, some (13, 3), some (26, 1), some (13, 1), some (7, 0), none, some (14, 0), some (16, 2), some (7, 2), some (53, 0), none, some (2, 3), some (31, 2), none, some (28, 0), none, some (38, 3), some (19, 2), some (3, 2), some (8, 0), none, some (48, 3), some (14, 2), some (18, 1), some (6, 3), none, some (19, 0), some (6, 1), some (43, 1), some (33, 0), none, some (43, 3), some (16, 1), some (23, 2), some (4, 3), none, some (9, 0), some (36, 2), some (33, 2), some (21, 3), none, some (41, 0), none, some (53, 2), some (24, 3), none, some (31, 0), some (26, 2), some (18, 2), some (23, 0), none, some (26, 0), some (11, 1), some (7, 1), some (11, 3), none, some (28, 3), some (14, 1), some (38, 2), some (16, 3), none, some (7, 3), some (6, 2), some (53, 1), some (43, 0), none, some (16, 0), some (4, 2), some (48, 1), some (31, 3), none, none, some (24, 2), some (28, 1), some (9, 3), none, some (11, 0), some (11, 2), some (28, 2), some (19, 3), none, some (3, 3), some (36, 1), some (8, 1), some (48, 0), none, some (12, 3), some (9, 2), some (38, 1), some (14, 3), none, some (36, 0), some (24, 1), some (12, 2), some (38, 0), none, some (24, 0), some (19, 1), some (12, 1), some (12, 0)]
def generators : Fin 2 → ℕ := ![2, 7]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q145
