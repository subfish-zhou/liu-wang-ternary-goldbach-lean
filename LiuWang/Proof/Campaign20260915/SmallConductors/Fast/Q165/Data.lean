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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q165

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), none, none, some (1, 2), some (2, 1), none, none, none, none, some (7, 2), some (1, 3), none, some (4, 0), some (16, 1), none, some (1, 4), none, none, none, some (14, 5), none, none, some (7, 3), none, some (2, 2), some (8, 7), none, some (14, 0), some (4, 1), none, some (23, 0), none, none, some (2, 6), some (1, 5), none, none, some (31, 7), none, some (17, 2), none, none, some (17, 4), some (7, 5), none, some (7, 0), none, none, some (14, 2), some (31, 5), none, none, some (2, 3), none, some (16, 6), some (4, 3), none, some (8, 4), some (14, 1), none, some (8, 0), none, none, some (23, 6), some (23, 1), none, none, some (8, 3), none, some (23, 2), some (2, 7), none, some (2, 4), none, none, some (16, 4), none, none, some (7, 6), some (17, 1), none, none, some (17, 3), none, none, some (31, 3), none, some (16, 0), some (17, 5), none, some (14, 4), none, none, some (8, 6), some (7, 1), none, none, some (1, 7), none, some (31, 6), some (14, 3), none, some (7, 4), some (31, 1), none, some (31, 4), none, none, some (4, 2), some (4, 5), none, none, some (16, 7), none, some (8, 2), some (16, 3), none, none, some (8, 5), none, some (17, 0), none, none, some (31, 2), some (8, 1), none, none, some (4, 7), none, some (1, 6), some (23, 7), none, some (31, 0), some (23, 5), none, some (4, 4), none, none, some (16, 2), none, none, none, some (23, 3), none, some (4, 6), some (17, 7), none, some (23, 4), some (2, 5), none, none, none, none, some (17, 6), some (16, 5), none, none, some (14, 7), none, some (14, 6), some (7, 7)]
def generators : Fin 3 → ℕ := ![2, 7, 19]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q165
