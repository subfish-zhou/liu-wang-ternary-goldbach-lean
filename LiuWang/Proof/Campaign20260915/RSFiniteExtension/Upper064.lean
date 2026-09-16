import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper063
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block064

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_14867 : UpperReach 14867 147198517034773 := by
  have hr := row_14867
  have hl := log_bounds hr.1
    (by change logScale (14867 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14851) (H := 147102448042025) (u := 96068992672)
    (by norm_num) (by norm_num) hr.1 gap_14867 hl.2
    (by norm_num) upper_reach_14851

theorem upper_reach_14869 : UpperReach 14869 147294587372692 := by
  have hr := row_14869
  have hl := log_bounds hr.1
    (by change logScale (14869 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14867) (H := 147198517034773) (u := 96070337843)
    (by norm_num) (by norm_num) hr.1 gap_14869 hl.2
    (by norm_num) upper_reach_14867

theorem upper_reach_14879 : UpperReach 14879 147390664433752 := by
  have hr := row_14879
  have hl := log_bounds hr.1
    (by change logScale (14879 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14869) (H := 147294587372692) (u := 96077060984)
    (by norm_num) (by norm_num) hr.1 gap_14879 hl.2
    (by norm_num) upper_reach_14869

theorem upper_reach_14887 : UpperReach 14887 147486746870072 := by
  have hr := row_14887
  have hl := log_bounds hr.1
    (by change logScale (14887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14879) (H := 147390664433752) (u := 96082436244)
    (by norm_num) (by norm_num) hr.1 gap_14887 hl.2
    (by norm_num) upper_reach_14879

theorem upper_reach_14891 : UpperReach 14891 147582831992940 := by
  have hr := row_14891
  have hl := log_bounds hr.1
    (by change logScale (14891 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14887) (H := 147486746870072) (u := 96085122792)
    (by norm_num) (by norm_num) hr.1 gap_14891 hl.2
    (by norm_num) upper_reach_14887

theorem upper_reach_14897 : UpperReach 14897 147678921144275 := by
  have hr := row_14897
  have hl := log_bounds hr.1
    (by change logScale (14897 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14891) (H := 147582831992940) (u := 96089151259)
    (by norm_num) (by norm_num) hr.1 gap_14897 hl.2
    (by norm_num) upper_reach_14891

theorem upper_reach_14923 : UpperReach 14923 147775027733576 := by
  have hr := row_14923
  have hl := log_bounds hr.1
    (by change logScale (14923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14897) (H := 147678921144275) (u := 96106589225)
    (by norm_num) (by norm_num) hr.1 gap_14923 hl.2
    (by norm_num) upper_reach_14897

theorem upper_reach_14929 : UpperReach 14929 147871138342708 := by
  have hr := row_14929
  have hl := log_bounds hr.1
    (by change logScale (14929 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14923) (H := 147775027733576) (u := 96110609056)
    (by norm_num) (by norm_num) hr.1 gap_14929 hl.2
    (by norm_num) upper_reach_14923

theorem upper_reach_14939 : UpperReach 14939 147967255647970 := by
  have hr := row_14939
  have hl := log_bounds hr.1
    (by change logScale (14939 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14929) (H := 147871138342708) (u := 96117305186)
    (by norm_num) (by norm_num) hr.1 gap_14939 hl.2
    (by norm_num) upper_reach_14929

theorem upper_reach_14947 : UpperReach 14947 148063378306910 := by
  have hr := row_14947
  have hl := log_bounds hr.1
    (by change logScale (14947 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14939) (H := 147967255647970) (u := 96122658864)
    (by norm_num) (by norm_num) hr.1 gap_14947 hl.2
    (by norm_num) upper_reach_14939

theorem upper_reach_14951 : UpperReach 14951 148159503641614 := by
  have hr := row_14951
  have hl := log_bounds hr.1
    (by change logScale (14951 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14947) (H := 148063378306910) (u := 96125334628)
    (by norm_num) (by norm_num) hr.1 gap_14951 hl.2
    (by norm_num) upper_reach_14947

theorem upper_reach_14957 : UpperReach 14957 148255632988622 := by
  have hr := row_14957
  have hl := log_bounds hr.1
    (by change logScale (14957 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14951) (H := 148159503641614) (u := 96129346932)
    (by norm_num) (by norm_num) hr.1 gap_14957 hl.2
    (by norm_num) upper_reach_14951

theorem upper_reach_14969 : UpperReach 14969 148351770355413 := by
  have hr := row_14969
  have hl := log_bounds hr.1
    (by change logScale (14969 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14957) (H := 148255632988622) (u := 96137366715)
    (by norm_num) (by norm_num) hr.1 gap_14969 hl.2
    (by norm_num) upper_reach_14957

theorem upper_reach_14983 : UpperReach 14983 148447917070495 := by
  have hr := row_14983
  have hl := log_bounds hr.1
    (by change logScale (14983 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14969) (H := 148351770355413) (u := 96146715006)
    (by norm_num) (by norm_num) hr.1 gap_14983 hl.2
    (by norm_num) upper_reach_14969

theorem upper_reach_15013 : UpperReach 15013 148544083788251 := by
  have hr := row_15013
  have hl := log_bounds hr.1
    (by change logScale (15013 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14983) (H := 148447917070495) (u := 96166717680)
    (by norm_num) (by norm_num) hr.1 gap_15013 hl.2
    (by norm_num) upper_reach_14983

theorem upper_reach_15017 : UpperReach 15017 148640253170010 := by
  have hr := row_15017
  have hl := log_bounds hr.1
    (by change logScale (15017 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15013) (H := 148544083788251) (u := 96169381683)
    (by norm_num) (by norm_num) hr.1 gap_15017 hl.2
    (by norm_num) upper_reach_15013

theorem upper_reach_15031 : UpperReach 15031 148736431870193 := by
  have hr := row_15031
  have hl := log_bounds hr.1
    (by change logScale (15031 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15017) (H := 148640253170010) (u := 96178700107)
    (by norm_num) (by norm_num) hr.1 gap_15031 hl.2
    (by norm_num) upper_reach_15017

theorem upper_reach_15053 : UpperReach 15053 148832625196093 := by
  have hr := row_15053
  have hl := log_bounds hr.1
    (by change logScale (15053 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15031) (H := 148736431870193) (u := 96193325824)
    (by norm_num) (by norm_num) hr.1 gap_15053 hl.2
    (by norm_num) upper_reach_15031

theorem upper_reach_15061 : UpperReach 15061 148928823835137 := by
  have hr := row_15061
  have hl := log_bounds hr.1
    (by change logScale (15061 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15053) (H := 148832625196093) (u := 96198638968)
    (by norm_num) (by norm_num) hr.1 gap_15061 hl.2
    (by norm_num) upper_reach_15053

theorem upper_reach_15073 : UpperReach 15073 149025030438607 := by
  have hr := row_15073
  have hl := log_bounds hr.1
    (by change logScale (15073 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15061) (H := 148928823835137) (u := 96206603394)
    (by norm_num) (by norm_num) hr.1 gap_15073 hl.2
    (by norm_num) upper_reach_15061

theorem upper_reach_15077 : UpperReach 15077 149121239695476 := by
  have hr := row_15077
  have hl := log_bounds hr.1
    (by change logScale (15077 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15073) (H := 149025030438607) (u := 96209256793)
    (by norm_num) (by norm_num) hr.1 gap_15077 hl.2
    (by norm_num) upper_reach_15073

theorem upper_reach_15083 : UpperReach 15083 149217452931125 := by
  have hr := row_15083
  have hl := log_bounds hr.1
    (by change logScale (15083 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15077) (H := 149121239695476) (u := 96213235573)
    (by norm_num) (by norm_num) hr.1 gap_15083 hl.2
    (by norm_num) upper_reach_15077

theorem upper_reach_15091 : UpperReach 15091 149313671469353 := by
  have hr := row_15091
  have hl := log_bounds hr.1
    (by change logScale (15091 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15083) (H := 149217452931125) (u := 96218538152)
    (by norm_num) (by norm_num) hr.1 gap_15091 hl.2
    (by norm_num) upper_reach_15083

theorem upper_reach_15101 : UpperReach 15101 149409896631852 := by
  have hr := row_15101
  have hl := log_bounds hr.1
    (by change logScale (15101 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15091) (H := 149313671469353) (u := 96225162423)
    (by norm_num) (by norm_num) hr.1 gap_15101 hl.2
    (by norm_num) upper_reach_15091

#print axioms upper_reach_15101

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
