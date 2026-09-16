import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper067
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block068

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_15749 : UpperReach 15749 156449902855113 := by
  have hr := row_15749
  have hl := log_bounds hr.1
    (by change logScale (15749 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15739) (H := 156353257533570) (u := 96645321467)
    (by norm_num) (by norm_num) hr.1 gap_15749 hl.2
    (by norm_num) upper_reach_15739

theorem upper_reach_15761 : UpperReach 15761 156546555793286 := by
  have hr := row_15761
  have hl := log_bounds hr.1
    (by change logScale (15761 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15749) (H := 156449902855113) (u := 96652938097)
    (by norm_num) (by norm_num) hr.1 gap_15761 hl.2
    (by norm_num) upper_reach_15749

theorem upper_reach_15767 : UpperReach 15767 156643212537600 := by
  have hr := row_15767
  have hl := log_bounds hr.1
    (by change logScale (15767 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15761) (H := 156546555793286) (u := 96656744238)
    (by norm_num) (by norm_num) hr.1 gap_15767 hl.2
    (by norm_num) upper_reach_15761

theorem upper_reach_15773 : UpperReach 15773 156739873086607 := by
  have hr := row_15773
  have hl := log_bounds hr.1
    (by change logScale (15773 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15767) (H := 156643212537600) (u := 96660548931)
    (by norm_num) (by norm_num) hr.1 gap_15773 hl.2
    (by norm_num) upper_reach_15767

theorem upper_reach_15787 : UpperReach 15787 156836542507604 := by
  have hr := row_15787
  have hl := log_bounds hr.1
    (by change logScale (15787 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15773) (H := 156739873086607) (u := 96669420921)
    (by norm_num) (by norm_num) hr.1 gap_15787 hl.2
    (by norm_num) upper_reach_15773

theorem upper_reach_15791 : UpperReach 15791 156933214462010 := by
  have hr := row_15791
  have hl := log_bounds hr.1
    (by change logScale (15791 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15787) (H := 156836542507604) (u := 96671954330)
    (by norm_num) (by norm_num) hr.1 gap_15791 hl.2
    (by norm_num) upper_reach_15787

theorem upper_reach_15797 : UpperReach 15797 157029890215327 := by
  have hr := row_15797
  have hl := log_bounds hr.1
    (by change logScale (15797 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15791) (H := 156933214462010) (u := 96675753241)
    (by norm_num) (by norm_num) hr.1 gap_15797 hl.2
    (by norm_num) upper_reach_15791

theorem upper_reach_15803 : UpperReach 15803 157126569766113 := by
  have hr := row_15803
  have hl := log_bounds hr.1
    (by change logScale (15803 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15797) (H := 157029890215327) (u := 96679550710)
    (by norm_num) (by norm_num) hr.1 gap_15803 hl.2
    (by norm_num) upper_reach_15797

theorem upper_reach_15809 : UpperReach 15809 157223253112926 := by
  have hr := row_15809
  have hl := log_bounds hr.1
    (by change logScale (15809 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15803) (H := 157126569766113) (u := 96683346737)
    (by norm_num) (by norm_num) hr.1 gap_15809 hl.2
    (by norm_num) upper_reach_15803

theorem upper_reach_15817 : UpperReach 15817 157319941518867 := by
  have hr := row_15817
  have hl := log_bounds hr.1
    (by change logScale (15817 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15809) (H := 157223253112926) (u := 96688405865)
    (by norm_num) (by norm_num) hr.1 gap_15817 hl.2
    (by norm_num) upper_reach_15809

theorem upper_reach_15823 : UpperReach 15823 157416633717476 := by
  have hr := row_15823
  have hl := log_bounds hr.1
    (by change logScale (15823 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15817) (H := 157319941518867) (u := 96692198533)
    (by norm_num) (by norm_num) hr.1 gap_15823 hl.2
    (by norm_num) upper_reach_15817

theorem upper_reach_15859 : UpperReach 15859 157513348641933 := by
  have hr := row_15859
  have hl := log_bounds hr.1
    (by change logScale (15859 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15823) (H := 157416633717476) (u := 96714924381)
    (by norm_num) (by norm_num) hr.1 gap_15859 hl.2
    (by norm_num) upper_reach_15823

theorem upper_reach_15877 : UpperReach 15877 157610074909975 := by
  have hr := row_15877
  have hl := log_bounds hr.1
    (by change logScale (15877 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15859) (H := 157513348641933) (u := 96726267966)
    (by norm_num) (by norm_num) hr.1 gap_15877 hl.2
    (by norm_num) upper_reach_15859

theorem upper_reach_15881 : UpperReach 15881 157706803697068 := by
  have hr := row_15881
  have hl := log_bounds hr.1
    (by change logScale (15881 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15877) (H := 157610074909975) (u := 96728787017)
    (by norm_num) (by norm_num) hr.1 gap_15881 hl.2
    (by norm_num) upper_reach_15877

theorem upper_reach_15887 : UpperReach 15887 157803536261547 := by
  have hr := row_15887
  have hl := log_bounds hr.1
    (by change logScale (15887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15881) (H := 157706803697068) (u := 96732564403)
    (by norm_num) (by norm_num) hr.1 gap_15887 hl.2
    (by norm_num) upper_reach_15881

theorem upper_reach_15889 : UpperReach 15889 157900270084838 := by
  have hr := row_15889
  have hl := log_bounds hr.1
    (by change logScale (15889 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15887) (H := 157803536261547) (u := 96733823215)
    (by norm_num) (by norm_num) hr.1 gap_15889 hl.2
    (by norm_num) upper_reach_15887

theorem upper_reach_15901 : UpperReach 15901 157997011457673 := by
  have hr := row_15901
  have hl := log_bounds hr.1
    (by change logScale (15901 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15889) (H := 157900270084838) (u := 96741372759)
    (by norm_num) (by norm_num) hr.1 gap_15901 hl.2
    (by norm_num) upper_reach_15889

theorem upper_reach_15907 : UpperReach 15907 158093756603144 := by
  have hr := row_15907
  have hl := log_bounds hr.1
    (by change logScale (15907 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15901) (H := 157997011457673) (u := 96745145395)
    (by norm_num) (by norm_num) hr.1 gap_15907 hl.2
    (by norm_num) upper_reach_15901

theorem upper_reach_15913 : UpperReach 15913 158190505519828 := by
  have hr := row_15913
  have hl := log_bounds hr.1
    (by change logScale (15913 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15907) (H := 158093756603144) (u := 96748916608)
    (by norm_num) (by norm_num) hr.1 gap_15913 hl.2
    (by norm_num) upper_reach_15907

theorem upper_reach_15919 : UpperReach 15919 158287258206303 := by
  have hr := row_15919
  have hl := log_bounds hr.1
    (by change logScale (15919 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15913) (H := 158190505519828) (u := 96752686399)
    (by norm_num) (by norm_num) hr.1 gap_15919 hl.2
    (by norm_num) upper_reach_15913

theorem upper_reach_15923 : UpperReach 15923 158384013405183 := by
  have hr := row_15923
  have hl := log_bounds hr.1
    (by change logScale (15923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15919) (H := 158287258206303) (u := 96755198804)
    (by norm_num) (by norm_num) hr.1 gap_15923 hl.2
    (by norm_num) upper_reach_15919

theorem upper_reach_15937 : UpperReach 15937 158480777392513 := by
  have hr := row_15937
  have hl := log_bounds hr.1
    (by change logScale (15937 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15923) (H := 158384013405183) (u := 96763987254)
    (by norm_num) (by norm_num) hr.1 gap_15937 hl.2
    (by norm_num) upper_reach_15923

theorem upper_reach_15959 : UpperReach 15959 158577555174679 := by
  have hr := row_15959
  have hl := log_bounds hr.1
    (by change logScale (15959 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15937) (H := 158480777392513) (u := 96777782090)
    (by norm_num) (by norm_num) hr.1 gap_15959 hl.2
    (by norm_num) upper_reach_15937

theorem upper_reach_15971 : UpperReach 15971 158674340473287 := by
  have hr := row_15971
  have hl := log_bounds hr.1
    (by change logScale (15971 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15959) (H := 158577555174679) (u := 96785298532)
    (by norm_num) (by norm_num) hr.1 gap_15971 hl.2
    (by norm_num) upper_reach_15959

#print axioms upper_reach_15971

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
