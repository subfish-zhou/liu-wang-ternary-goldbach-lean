import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper068
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block069

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_15973 : UpperReach 15973 158771127024087 := by
  have hr := row_15973
  have hl := log_bounds hr.1
    (by change logScale (15973 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15971) (H := 158674340473287) (u := 96786550724)
    (by norm_num) (by norm_num) hr.1 gap_15973 hl.2
    (by norm_num) upper_reach_15971

theorem upper_reach_15991 : UpperReach 15991 158867924837558 := by
  have hr := row_15991
  have hl := log_bounds hr.1
    (by change logScale (15991 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15973) (H := 158771127024087) (u := 96797813395)
    (by norm_num) (by norm_num) hr.1 gap_15991 hl.2
    (by norm_num) upper_reach_15973

#print axioms upper_reach_15991

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
