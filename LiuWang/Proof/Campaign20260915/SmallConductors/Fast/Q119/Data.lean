import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q119

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (11, 0), some (1, 1), some (2, 0), some (9, 1), some (11, 1), none, some (22, 0), some (3, 0), some (20, 1), some (1, 2), some (2, 1), some (2, 3), none, some (27, 0), some (4, 0), none, some (16, 0), some (27, 3), some (18, 1), none, some (11, 2), some (30, 2), some (22, 1), some (5, 0), some (22, 3), some (3, 1), none, some (10, 2), some (25, 0), some (13, 1), some (44, 0), some (1, 3), none, none, some (6, 0), some (5, 2), some (25, 3), some (6, 2), some (23, 1), some (39, 1), none, some (20, 0), some (2, 2), some (27, 1), some (27, 2), some (15, 3), some (4, 1), none, some (13, 0), none, some (4, 3), some (23, 0), some (16, 1), some (9, 3), none, some (4, 2), some (9, 2), some (3, 3), some (37, 0), some (37, 1), some (10, 1), none, some (8, 0), some (37, 2), some (11, 3), some (30, 0), none, some (30, 3), none, some (39, 2), some (32, 0), some (8, 1), some (13, 2), some (5, 1), some (37, 3), none, some (32, 2), some (16, 2), some (15, 1), some (9, 0), some (30, 1), some (23, 3), none, none, some (18, 0), some (10, 3), some (22, 2), some (8, 3), some (25, 1), none, some (25, 2), some (39, 0), some (39, 3), some (15, 2), some (44, 1), some (32, 1), none, some (3, 2), some (10, 0), some (18, 3), none, some (13, 3), some (44, 3), none, some (15, 0), some (23, 2), some (6, 1), some (8, 2), some (20, 3), some (5, 3), none, some (18, 2), some (44, 2), some (32, 3), some (20, 2), some (6, 3), some (16, 3)]
def generators : Fin 2 → ℕ := ![3, 11]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q119
