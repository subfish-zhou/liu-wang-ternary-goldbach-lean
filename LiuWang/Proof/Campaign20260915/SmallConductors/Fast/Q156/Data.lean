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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q156

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, some (1, 2), none, none, none, some (1, 4), none, none, none, none, none, some (23, 6), none, some (5, 2), none, none, none, some (11, 3), none, some (5, 0), none, none, none, some (7, 6), none, some (7, 2), none, none, none, some (1, 3), none, some (17, 7), none, none, none, some (17, 1), none, some (7, 5), none, none, none, some (23, 4), none, some (7, 0), none, none, none, some (5, 6), none, some (1, 5), none, none, none, some (17, 4), none, some (23, 0), none, none, none, none, none, some (11, 2), none, none, none, some (7, 4), none, some (1, 7), none, none, none, some (1, 6), none, some (23, 5), none, none, none, some (11, 4), none, some (23, 7), none, none, none, some (7, 1), none, none, none, none, none, some (5, 3), none, some (11, 7), none, none, none, some (17, 6), none, some (11, 5), none, none, none, some (23, 3), none, some (5, 7), none, none, none, some (11, 6), none, some (23, 2), none, none, none, some (5, 4), none, some (11, 0), none, none, none, some (5, 1), none, some (5, 5), none, none, none, some (17, 3), none, some (17, 0), none, none, none, some (11, 1), none, some (17, 5), none, none, none, none, none, some (7, 7), none, none, none, some (23, 1), none, some (17, 2), none, none, none, some (7, 3)]
def generators : Fin 3 → ℕ := ![5, 7, 11]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q156
