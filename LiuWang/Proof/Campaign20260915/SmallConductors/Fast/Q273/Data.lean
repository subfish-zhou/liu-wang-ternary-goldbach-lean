import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListCover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Imprimitive
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Envelope2533_2500

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q273

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (1, 2), none, none, some (2, 1), none, some (1, 3), some (31, 1), none, none, none, none, some (4, 0), some (1, 4), none, some (11, 5), some (2, 2), none, some (29, 0), some (20, 7), none, some (5, 0), none, none, none, some (61, 7), none, some (5, 5), some (4, 1), none, some (1, 5), none, none, some (10, 6), some (22, 4), none, some (2, 3), some (61, 2), none, some (41, 0), some (29, 1), none, some (40, 6), some (8, 2), none, none, some (5, 1), none, none, some (25, 7), none, some (31, 3), none, none, some (31, 6), some (11, 2), none, some (19, 3), some (10, 4), none, some (8, 0), none, none, some (2, 6), some (2, 4), none, none, some (61, 1), none, some (40, 5), some (10, 7), none, some (22, 5), none, none, some (25, 0), some (4, 2), none, some (61, 3), some (40, 2), none, some (1, 6), some (41, 1), none, some (19, 0), some (20, 2), none, none, some (40, 7), none, some (8, 3), some (11, 7), none, some (41, 5), none, none, some (10, 0), some (29, 4), none, some (16, 3), none, none, some (41, 6), some (22, 7), none, some (19, 6), some (29, 2), none, none, some (16, 7), none, some (61, 5), some (31, 7), none, some (11, 3), none, none, some (11, 0), some (25, 2), none, some (10, 5), some (5, 2), none, some (20, 0), some (8, 1), none, none, some (19, 4), none, none, some (2, 7), none, some (2, 5), some (32, 1), none, some (32, 3), none, none, some (31, 0), none, none, some (32, 5), some (11, 4), none, some (20, 6), some (22, 1), none, some (61, 6), some (5, 4), none, none, some (5, 7), none, some (41, 3), some (25, 1), none, some (4, 3), none, none, some (25, 6), some (31, 2), none, some (40, 3), some (19, 2), none, none, some (1, 7), none, some (61, 0), some (40, 4), none, none, some (19, 1), none, some (20, 3), some (32, 7), none, some (10, 3), none, none, some (11, 6), some (41, 4), none, some (31, 5), some (16, 2), none, some (22, 6), some (29, 7), none, some (16, 6), some (61, 4), none, none, some (40, 1), none, some (22, 3), some (10, 1), none, some (29, 5), none, none, some (32, 0), some (32, 2), none, none, some (32, 4), none, some (22, 0), some (41, 7), none, some (5, 6), some (41, 2), none, none, some (19, 7), none, some (29, 3), none, none, some (20, 5), none, none, some (32, 6), some (10, 2), none, some (25, 5), some (31, 4), none, some (29, 6), some (8, 7), none, some (40, 0), some (22, 2), none, none, some (16, 1), none, some (16, 5), some (11, 1), none, some (25, 3), none, none, none, some (20, 4), none, some (5, 3), some (25, 4), none, some (8, 6), some (20, 1), none, some (16, 0), some (16, 4), none, none, none, none, some (19, 5), some (4, 7), none, some (8, 5), none, none, some (4, 6), some (8, 4), none, some (4, 5), some (4, 4)]
def generators : Fin 3 → ℕ := ![2, 5, 17]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q273
