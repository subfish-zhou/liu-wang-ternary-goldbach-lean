import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q143

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (17, 0), some (2, 0), some (1, 2), some (17, 1), some (19, 1), some (2, 1), some (3, 0), some (1, 3), none, some (21, 0), none, some (27, 0), some (17, 2), some (4, 0), some (4, 3), some (3, 1), some (9, 1), some (2, 2), some (15, 1), none, some (32, 0), some (21, 1), some (5, 0), none, some (40, 0), some (27, 1), some (31, 3), some (17, 3), some (53, 2), some (4, 1), none, some (8, 2), some (19, 3), some (6, 0), some (6, 2), some (18, 0), none, some (2, 3), some (53, 1), some (30, 0), some (43, 3), none, some (3, 2), some (32, 1), some (18, 2), some (42, 0), some (7, 0), some (5, 1), some (42, 3), none, some (14, 0), some (40, 1), none, some (54, 0), some (10, 1), some (29, 2), some (28, 2), some (21, 2), some (7, 3), some (53, 3), some (31, 1), some (8, 0), none, none, some (30, 2), some (8, 3), some (28, 0), some (27, 2), some (10, 2), some (6, 1), some (41, 1), some (6, 3), some (19, 0), some (18, 1), none, none, some (41, 3), some (4, 2), some (9, 0), some (15, 0), some (16, 1), some (30, 1), some (20, 1), some (31, 2), some (32, 3), none, some (19, 2), some (3, 3), none, some (53, 0), some (43, 2), some (18, 3), some (9, 3), some (42, 1), some (42, 2), some (7, 1), none, some (10, 0), some (14, 3), some (7, 2), some (31, 0), none, some (15, 3), some (14, 1), some (5, 3), some (41, 0), some (29, 1), none, some (41, 2), some (54, 1), some (16, 0), some (20, 0), some (32, 2), some (29, 3), none, some (28, 3), some (9, 2), some (21, 3), none, some (14, 2), some (43, 1), some (15, 2), some (5, 2), some (29, 0), some (40, 3), some (8, 1), some (16, 3), none, some (54, 3), none, some (43, 0), some (30, 3), some (40, 2), some (16, 2), some (54, 2), some (28, 1), some (20, 3), some (27, 3), some (20, 2), some (10, 3)]
def generators : Fin 2 → ℕ := ![2, 5]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q143
