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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q164

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (13, 0), none, some (37, 1), none, some (3, 0), none, some (21, 1), none, some (1, 2), none, some (13, 1), none, some (35, 2), none, some (15, 1), none, some (29, 0), none, some (3, 3), none, some (5, 0), none, some (3, 1), none, some (31, 2), none, some (13, 3), none, some (19, 0), none, some (11, 1), none, some (23, 0), none, some (1, 3), none, none, none, some (9, 3), none, some (39, 0), none, some (17, 1), none, some (7, 0), none, some (35, 3), none, some (33, 2), none, some (27, 1), none, some (37, 0), none, some (27, 3), none, some (15, 0), none, some (29, 1), none, some (13, 2), none, some (35, 1), none, some (9, 2), none, some (25, 1), none, some (27, 0), none, some (5, 1), none, some (35, 0), none, some (9, 1), none, some (9, 0), none, some (15, 3), none, some (37, 2), none, some (31, 3), none, some (25, 2), none, some (37, 3), none, some (39, 2), none, some (31, 1), none, some (11, 2), none, some (19, 1), none, some (19, 2), none, some (25, 3), none, some (33, 0), none, some (7, 3), none, some (29, 2), none, some (23, 1), none, some (21, 0), none, some (39, 3), none, some (3, 2), none, some (17, 3), none, some (11, 0), none, none, none, some (17, 0), none, some (11, 3), none, some (27, 2), none, some (23, 3), none, some (25, 0), none, some (39, 1), none, some (15, 2), none, some (19, 3), none, some (31, 0), none, some (21, 3), none, some (7, 2), none, some (7, 1), none, some (17, 2), none, some (33, 1), none, some (23, 2), none, some (5, 3), none, some (21, 2), none, some (33, 3), none, some (5, 2), none, some (29, 3)]
def generators : Fin 2 → ℕ := ![3, 13]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q164
