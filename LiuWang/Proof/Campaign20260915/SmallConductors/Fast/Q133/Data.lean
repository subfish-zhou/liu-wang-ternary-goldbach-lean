import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q133

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), some (17, 3), some (1, 3), none, some (2, 1), some (3, 0), some (15, 2), some (12, 0), some (2, 2), some (25, 2), none, some (44, 1), some (4, 0), some (5, 3), some (3, 1), none, some (15, 3), none, some (12, 1), some (17, 0), some (2, 3), some (5, 0), some (25, 3), some (3, 2), none, some (9, 1), some (31, 0), some (36, 2), some (4, 1), some (12, 2), some (10, 2), none, some (6, 0), some (22, 1), none, some (37, 0), some (30, 2), some (18, 2), none, some (29, 0), some (24, 0), some (44, 3), some (17, 1), some (31, 3), some (4, 2), none, some (5, 1), some (15, 1), some (50, 2), some (25, 1), some (3, 3), some (43, 3), none, none, some (18, 0), some (8, 2), some (31, 1), some (11, 3), some (36, 3), none, some (8, 0), some (36, 1), some (12, 3), some (10, 1), some (10, 3), some (17, 2), none, some (30, 1), some (6, 1), some (16, 3), some (44, 0), some (5, 2), none, none, some (37, 1), some (50, 1), some (30, 3), some (9, 0), some (18, 3), some (6, 3), none, some (22, 0), some (29, 1), some (9, 3), some (24, 1), some (44, 2), some (31, 2), none, some (15, 0), some (25, 0), some (43, 2), none, some (4, 3), some (11, 2), none, some (36, 0), some (10, 0), some (37, 3), some (30, 0), some (16, 2), some (50, 3), none, some (50, 0), some (43, 1), some (6, 2), some (11, 1), some (9, 2), some (22, 3), none, some (16, 1), none, some (23, 3), some (18, 1), some (37, 2), some (8, 3), none, some (43, 0), some (11, 0), some (22, 2), some (16, 0), some (23, 2), some (29, 3), none, some (23, 1), some (8, 1), some (29, 2), some (23, 0), some (24, 3), some (24, 2)]
def generators : Fin 2 → ℕ := ![2, 3]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q133
