import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover00
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover01
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover02
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover03
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover04
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover05
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover06
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover07
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover08
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover09
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover10
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover11
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover12
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover13
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover14
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover15
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover16
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover17
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover18
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover19
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover20
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover21
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover22
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover23
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover24
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover25
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover26
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover27
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover28
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover29
import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Cover30

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985

theorem cover : SquareWordCover 985 generators words := by
  apply cover_of_blocks generators words (width := 32) (blocks := 31)
    (by decide) (by decide)
  intro b
  fin_cases b
  · exact cover00
  · exact cover01
  · exact cover02
  · exact cover03
  · exact cover04
  · exact cover05
  · exact cover06
  · exact cover07
  · exact cover08
  · exact cover09
  · exact cover10
  · exact cover11
  · exact cover12
  · exact cover13
  · exact cover14
  · exact cover15
  · exact cover16
  · exact cover17
  · exact cover18
  · exact cover19
  · exact cover20
  · exact cover21
  · exact cover22
  · exact cover23
  · exact cover24
  · exact cover25
  · exact cover26
  · exact cover27
  · exact cover28
  · exact cover29
  · exact cover30

#print axioms cover

end LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985
