import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (17, 1), some (2, 0), none, some (11, 0), some (1, 2), some (2, 1), some (3, 0), none, some (3, 3), some (11, 1), some (8, 1), some (1, 3), none, some (4, 0), some (26, 2), some (3, 1), some (16, 3), none, some (17, 3), some (6, 2), none, some (22, 0), none, some (16, 0), some (41, 1), some (2, 2), some (12, 0), none, some (36, 0), some (4, 1), some (13, 2), some (26, 3), none, some (6, 0), some (41, 2), some (32, 2), some (27, 0), none, some (31, 0), some (11, 2), some (27, 2), some (6, 3), none, none, some (9, 1), some (22, 1), some (7, 0), none, some (18, 3), some (16, 1), some (22, 2), some (13, 0), none, some (2, 3), some (31, 2), some (12, 1), some (17, 0), none, some (12, 3), some (36, 1), some (3, 2), some (8, 0), none, some (13, 3), some (16, 2), some (17, 2), none, none, some (41, 0), some (6, 1), some (18, 1), some (41, 3), none, some (32, 3), some (21, 1), some (27, 1), some (21, 3), none, some (9, 0), some (31, 1), some (18, 2), some (11, 3), none, some (27, 3), some (26, 1), some (12, 2), some (36, 3), none, some (8, 3), none, some (32, 1), some (18, 0), none, some (21, 0), some (21, 2), some (7, 1), some (9, 3), none, some (26, 0), some (36, 2), some (8, 2), some (32, 0), none, some (22, 3), some (9, 2), some (13, 1), some (4, 3), none, some (7, 3), some (4, 2), some (7, 2), some (31, 3)]
def generators : Fin 2 → ℕ := ![2, 7]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115
