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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q308

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (1, 2), none, none, none, some (3, 0), none, none, none, some (1, 4), none, some (1, 3), none, some (5, 4), none, some (45, 7), none, none, none, some (17, 3), none, some (5, 0), none, some (3, 1), none, some (9, 6), none, some (27, 1), none, none, none, none, none, some (31, 0), none, some (1, 5), none, some (13, 4), none, some (3, 5), none, some (3, 2), none, some (23, 1), none, none, none, some (5, 5), none, some (19, 0), none, none, none, some (19, 6), none, some (15, 1), none, some (17, 4), none, none, none, some (1, 6), none, some (5, 3), none, some (37, 2), none, some (13, 3), none, some (19, 4), none, some (5, 1), none, none, none, some (9, 5), none, some (9, 0), none, some (41, 7), none, some (5, 6), none, some (9, 7), none, some (41, 2), none, none, none, some (59, 0), none, some (27, 5), none, some (9, 2), none, none, none, some (23, 4), none, some (37, 1), none, none, none, some (37, 5), none, some (45, 6), none, some (31, 1), none, some (27, 0), none, some (41, 1), none, some (3, 4), none, none, none, none, none, some (13, 5), none, some (5, 2), none, some (45, 5), none, some (9, 4), none, some (31, 7), none, none, none, some (3, 3), none, some (37, 0), none, some (15, 7), none, some (41, 0), none, none, none, some (45, 4), none, none, none, some (15, 6), none, some (15, 5), none, some (15, 4), none, some (27, 3), none, some (59, 2), none, some (19, 1), none, none, none, some (59, 3), none, none, none, some (27, 7), none, some (13, 0), none, some (19, 7), none, some (31, 4), none, none, none, some (45, 0), none, some (19, 3), none, some (23, 2), none, some (17, 5), none, some (31, 2), none, none, none, none, none, some (45, 3), none, some (59, 6), none, some (1, 7), none, some (23, 6), none, some (13, 1), none, some (15, 2), none, none, none, some (13, 6), none, some (37, 3), none, none, none, some (31, 5), none, some (17, 2), none, some (3, 7), none, none, none, some (19, 5), none, some (23, 0), none, some (45, 1), none, some (15, 0), none, some (37, 7), none, some (13, 2), none, none, none, some (41, 6), none, some (23, 3), none, some (27, 4), none, some (59, 5), none, some (37, 4), none, some (9, 1), none, none, none, some (31, 3), none, some (31, 6), none, some (17, 1), none, none, none, some (5, 7), none, some (27, 2), none, none, none, some (27, 6), none, some (41, 5), none, some (19, 2), none, some (41, 3), none, some (45, 2), none, some (59, 7), none, none, none, none, none, some (3, 6), none, some (59, 1), none, some (37, 6), none, some (23, 7), none, some (59, 4), none, none, none, some (17, 0), none, some (9, 3), none, some (41, 4), none, some (15, 3), none, none, none, some (17, 7), none, none, none, some (23, 5), none, some (17, 6), none, some (13, 7)]
def generators : Fin 3 → ℕ := ![3, 5, 13]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q308
