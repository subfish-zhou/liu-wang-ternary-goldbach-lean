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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q220

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, none, none, some (1, 2), none, some (3, 0), none, none, none, some (1, 4), none, none, none, some (17, 4), none, some (29, 5), none, some (1, 3), none, some (9, 1), none, none, none, some (3, 1), none, some (13, 3), none, some (39, 6), none, none, none, none, none, some (3, 7), none, some (1, 5), none, some (39, 3), none, some (17, 2), none, none, none, some (23, 1), none, some (7, 0), none, some (17, 5), none, some (1, 7), none, none, none, some (23, 4), none, some (7, 6), none, some (29, 3), none, some (3, 2), none, none, none, some (13, 1), none, some (17, 0), none, some (19, 6), none, some (19, 4), none, none, none, none, none, some (9, 5), none, some (9, 0), none, some (13, 2), none, none, none, some (39, 2), none, some (23, 0), none, some (1, 6), none, some (39, 7), none, none, none, some (23, 7), none, none, none, some (19, 3), none, some (29, 1), none, none, none, some (19, 2), none, some (23, 3), none, some (9, 6), none, some (9, 7), none, none, none, some (3, 4), none, some (17, 6), none, none, none, some (7, 2), none, none, none, some (9, 2), none, some (17, 3), none, some (3, 5), none, some (29, 7), none, none, none, some (17, 7), none, some (39, 5), none, some (19, 0), none, none, none, none, none, some (7, 1), none, some (7, 3), none, some (7, 5), none, some (29, 4), none, none, none, some (13, 7), none, some (3, 6), none, some (9, 3), none, some (39, 1), none, none, none, some (29, 2), none, some (13, 0), none, some (23, 5), none, some (9, 4), none, none, none, some (7, 7), none, some (23, 6), none, some (29, 0), none, some (23, 2), none, none, none, none, none, some (3, 3), none, some (29, 6), none, some (39, 4), none, none, none, some (7, 4), none, some (13, 6), none, some (39, 0), none, some (19, 1), none, none, none, some (17, 1), none, none, none, some (13, 5), none, some (19, 7), none, none, none, some (13, 4), none, some (19, 5)]
def generators : Fin 3 → ℕ := ![3, 7, 13]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q220
