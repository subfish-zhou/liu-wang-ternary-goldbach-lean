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

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q340

def words : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, none, none, some (63, 1), none, some (3, 0), none, some (1, 2), none, some (19, 3), none, none, none, none, none, some (1, 4), none, some (19, 0), none, some (11, 1), none, none, none, some (3, 1), none, some (21, 6), none, some (31, 2), none, some (1, 3), none, none, none, some (31, 5), none, some (23, 2), none, some (7, 6), none, some (53, 7), none, none, none, some (11, 7), none, some (7, 0), none, none, none, some (41, 3), none, none, none, some (1, 5), none, some (19, 4), none, some (23, 6), none, some (19, 1), none, none, none, some (31, 7), none, some (33, 0), none, some (29, 2), none, some (7, 5), none, none, none, some (63, 3), none, some (33, 2), none, some (9, 0), none, some (33, 7), none, none, none, some (21, 7), none, some (53, 0), none, some (21, 2), none, some (31, 3), none, none, none, some (11, 5), none, some (3, 2), none, some (21, 0), none, some (63, 7), none, none, none, some (43, 1), none, some (41, 6), none, some (43, 4), none, some (13, 5), none, none, none, some (23, 3), none, none, none, some (11, 0), none, some (7, 7), none, none, none, some (9, 7), none, some (11, 6), none, some (41, 2), none, some (63, 5), none, none, none, some (13, 3), none, some (63, 2), none, some (33, 6), none, some (29, 1), none, none, none, some (7, 1), none, some (43, 0), none, some (13, 4), none, none, none, none, none, some (43, 3), none, some (13, 2), none, some (29, 0), none, some (31, 1), none, none, none, some (13, 1), none, some (13, 0), none, some (3, 4), none, some (3, 5), none, none, none, some (19, 5), none, some (9, 4), none, some (3, 6), none, some (23, 7), none, none, none, none, none, some (23, 0), none, some (23, 4), none, some (33, 5), none, none, none, some (9, 5), none, some (7, 2), none, some (43, 6), none, some (3, 7), none, none, none, some (33, 1), none, some (1, 6), none, some (9, 2), none, some (29, 3), none, none, none, some (53, 3), none, some (21, 4), none, none, none, some (13, 7), none, none, none, some (23, 1), none, some (63, 0), none, some (19, 2), none, some (23, 5), none, none, none, some (33, 3), none, some (31, 4), none, some (53, 6), none, some (9, 1), none, none, none, some (19, 7), none, some (31, 6), none, some (7, 4), none, some (11, 3), none, none, none, some (7, 3), none, some (11, 4), none, some (63, 6), none, some (43, 7), none, none, none, some (53, 1), none, some (9, 6), none, some (63, 4), none, some (21, 3), none, none, none, some (41, 5), none, some (43, 2), none, some (31, 0), none, some (41, 1), none, none, none, some (1, 7), none, none, none, some (33, 4), none, some (9, 3), none, none, none, some (3, 3), none, some (53, 2), none, some (13, 6), none, some (21, 1), none, none, none, some (29, 7), none, some (19, 6), none, some (11, 2), none, some (53, 5), none, none, none, some (21, 5), none, some (41, 4), none, some (41, 0), none, none, none, none, none, some (41, 7), none, some (29, 6), none, some (53, 4), none, some (43, 5), none, none, none, some (29, 5), none, some (29, 4)]
def generators : Fin 3 → ℕ := ![3, 11, 19]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q340
