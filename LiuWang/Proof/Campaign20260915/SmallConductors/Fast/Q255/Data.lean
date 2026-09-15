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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q255

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), none, none, some (1, 2), some (2, 1), none, none, some (23, 3), none, some (1, 4), some (1, 3), none, some (4, 0), none, none, some (23, 0), none, none, some (29, 2), some (37, 7), none, none, some (1, 5), none, some (2, 2), some (26, 3), none, some (29, 6), some (4, 1), none, none, none, none, some (41, 2), some (23, 1), none, none, some (37, 3), none, some (11, 4), some (29, 3), none, some (11, 6), some (41, 1), none, some (7, 0), none, none, some (2, 4), some (52, 1), none, none, some (2, 3), none, some (52, 2), some (13, 5), none, some (26, 6), some (29, 7), none, some (8, 0), none, none, some (8, 4), none, none, none, some (13, 3), none, some (22, 2), some (41, 3), none, some (29, 0), some (26, 1), none, some (13, 6), none, none, some (11, 2), some (13, 1), none, none, some (11, 5), none, some (7, 2), some (22, 5), none, some (1, 6), some (11, 7), none, some (37, 0), none, none, some (14, 2), some (7, 1), none, none, some (41, 5), none, some (19, 4), some (2, 5), none, some (19, 0), some (4, 7), none, some (2, 6), none, none, some (4, 2), some (22, 7), none, none, some (52, 3), none, some (26, 4), none, none, some (11, 0), some (26, 7), none, some (7, 6), none, none, some (7, 4), some (8, 1), none, none, some (8, 3), none, some (23, 2), some (8, 5), none, none, some (14, 1), none, some (37, 6), none, none, some (26, 2), some (23, 7), none, none, some (22, 3), none, some (37, 2), some (37, 5), none, some (41, 0), some (29, 1), none, some (52, 0), none, none, some (13, 4), some (13, 7), none, none, some (4, 5), none, some (13, 2), some (11, 3), none, some (26, 0), some (19, 7), none, some (13, 0), none, none, some (22, 4), some (8, 7), none, none, some (7, 3), none, some (41, 4), some (52, 5), none, some (4, 6), some (1, 7), none, some (22, 6), none, none, none, some (37, 1), none, none, some (29, 5), none, some (8, 2), some (14, 3), none, some (14, 0), some (41, 7), none, some (23, 6), none, none, some (37, 4), some (22, 1), none, none, some (19, 5), none, some (4, 4), some (19, 3), none, some (19, 6), some (19, 1), none, some (8, 6), none, none, some (52, 4), some (2, 7), none, none, none, none, some (29, 4), some (4, 3), none, some (41, 6), some (14, 7), none, some (22, 0), none, none, some (19, 2), some (52, 7), none, none, some (26, 5), none, none, some (23, 5), none, some (14, 6), some (11, 1), none, some (52, 6), none, none, some (23, 4), some (7, 7), none, none, some (14, 5), none, some (14, 4), some (7, 5)]
def generators : Fin 3 → ℕ := ![2, 7, 13]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q255
