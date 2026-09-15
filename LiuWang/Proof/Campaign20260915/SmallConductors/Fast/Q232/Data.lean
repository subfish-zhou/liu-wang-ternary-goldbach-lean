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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q232

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (1, 2), none, some (1, 4), none, some (3, 0), none, some (9, 1), none, some (7, 2), none, some (1, 3), none, some (3, 7), none, some (25, 1), none, some (1, 5), none, some (13, 4), none, some (5, 0), none, some (3, 1), none, none, none, some (27, 3), none, some (27, 0), none, some (1, 6), none, some (17, 5), none, some (7, 3), none, some (7, 7), none, some (13, 1), none, some (3, 2), none, some (23, 3), none, some (7, 0), none, some (9, 6), none, some (17, 2), none, some (9, 3), none, some (17, 0), none, some (11, 6), none, some (5, 5), none, some (3, 4), none, some (23, 0), none, some (25, 6), none, some (13, 5), none, some (21, 4), none, some (5, 7), none, some (5, 1), none, some (9, 5), none, some (19, 3), none, some (9, 0), none, some (3, 6), none, some (15, 5), none, none, none, some (19, 7), none, some (7, 6), none, some (23, 2), none, some (25, 3), none, some (23, 7), none, some (27, 1), none, some (7, 5), none, some (9, 4), none, some (1, 7), none, some (19, 6), none, some (25, 2), none, some (7, 4), none, some (13, 7), none, some (13, 6), none, some (21, 2), none, some (21, 3), none, some (11, 0), none, some (21, 6), none, some (5, 2), none, some (15, 3), none, some (19, 0), none, some (11, 1), none, some (25, 5), none, some (3, 3), none, some (21, 7), none, some (17, 6), none, some (11, 2), none, some (5, 3), none, none, none, some (7, 1), none, some (13, 2), none, some (11, 4), none, some (9, 7), none, some (19, 1), none, some (19, 5), none, some (17, 3), none, some (25, 0), none, some (21, 1), none, some (27, 2), none, some (17, 4), none, some (13, 0), none, some (17, 1), none, some (9, 2), none, some (5, 4), none, some (11, 7), none, some (5, 6), none, some (19, 2), none, some (15, 4), none, some (17, 7), none, some (23, 6), none, some (3, 5), none, some (11, 3), none, some (15, 7), none, some (23, 1), none, some (15, 2), none, some (25, 4), none, some (25, 7), none, none, none, some (23, 5), none, some (19, 4), none, some (21, 0), none, some (15, 1), none, some (21, 5), none, some (13, 3), none, some (27, 7), none, some (15, 6), none, some (11, 5), none, some (23, 4), none, some (15, 0), none, some (27, 6), none, some (27, 5), none, some (27, 4)]
def generators : Fin 3 → ℕ := ![3, 5, 7]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q232
