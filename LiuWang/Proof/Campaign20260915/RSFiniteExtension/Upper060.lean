import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper059
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block060

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_13913 : UpperReach 13913 138004855426802 := by
  have hr := row_13913
  have hl := log_bounds hr.1
    (by change logScale (13913 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13907) (H := 137909449637422) (u := 95405789304)
    (by norm_num) (by norm_num) hr.1 gap_13913 hl.2
    (by norm_num) upper_reach_13907

theorem upper_reach_13921 : UpperReach 13921 138100266964548 := by
  have hr := row_13921
  have hl := log_bounds hr.1
    (by change logScale (13921 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13913) (H := 138004855426802) (u := 95411537670)
    (by norm_num) (by norm_num) hr.1 gap_13921 hl.2
    (by norm_num) upper_reach_13913

theorem upper_reach_13931 : UpperReach 13931 138195685683107 := by
  have hr := row_13931
  have hl := log_bounds hr.1
    (by change logScale (13931 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13921) (H := 138100266964548) (u := 95418718483)
    (by norm_num) (by norm_num) hr.1 gap_13931 hl.2
    (by norm_num) upper_reach_13921

theorem upper_reach_13933 : UpperReach 13933 138291105837210 := by
  have hr := row_13933
  have hl := log_bounds hr.1
    (by change logScale (13933 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13931) (H := 138195685683107) (u := 95420154027)
    (by norm_num) (by norm_num) hr.1 gap_13933 hl.2
    (by norm_num) upper_reach_13931

theorem upper_reach_13963 : UpperReach 13963 138386547499781 := by
  have hr := row_13963
  have hl := log_bounds hr.1
    (by change logScale (13963 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13933) (H := 138291105837210) (u := 95441662495)
    (by norm_num) (by norm_num) hr.1 gap_13963 hl.2
    (by norm_num) upper_reach_13933

theorem upper_reach_13967 : UpperReach 13967 138481992026656 := by
  have hr := row_13967
  have hl := log_bounds hr.1
    (by change logScale (13967 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13963) (H := 138386547499781) (u := 95444526799)
    (by norm_num) (by norm_num) hr.1 gap_13967 hl.2
    (by norm_num) upper_reach_13963

theorem upper_reach_13997 : UpperReach 13997 138577458009697 := by
  have hr := row_13997
  have hl := log_bounds hr.1
    (by change logScale (13997 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13967) (H := 138481992026656) (u := 95465982965)
    (by norm_num) (by norm_num) hr.1 gap_13997 hl.2
    (by norm_num) upper_reach_13967

theorem upper_reach_13999 : UpperReach 13999 138672925421513 := by
  have hr := row_13999
  have hl := log_bounds hr.1
    (by change logScale (13999 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13997) (H := 138577458009697) (u := 95467411740)
    (by norm_num) (by norm_num) hr.1 gap_13999 hl.2
    (by norm_num) upper_reach_13997

theorem upper_reach_14009 : UpperReach 14009 138768399974147 := by
  have hr := row_14009
  have hl := log_bounds hr.1
    (by change logScale (14009 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13999) (H := 138672925421513) (u := 95474552558)
    (by norm_num) (by norm_num) hr.1 gap_14009 hl.2
    (by norm_num) upper_reach_13999

theorem upper_reach_14011 : UpperReach 14011 138863875954332 := by
  have hr := row_14011
  have hl := log_bounds hr.1
    (by change logScale (14011 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14009) (H := 138768399974147) (u := 95475980109)
    (by norm_num) (by norm_num) hr.1 gap_14011 hl.2
    (by norm_num) upper_reach_14009

theorem upper_reach_14029 : UpperReach 14029 138959364773321 := by
  have hr := row_14029
  have hl := log_bounds hr.1
    (by change logScale (14029 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14011) (H := 138863875954332) (u := 95488818913)
    (by norm_num) (by norm_num) hr.1 gap_14029 hl.2
    (by norm_num) upper_reach_14011

theorem upper_reach_14033 : UpperReach 14033 139054856443140 := by
  have hr := row_14033
  have hl := log_bounds hr.1
    (by change logScale (14033 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14029) (H := 138959364773321) (u := 95491669743)
    (by norm_num) (by norm_num) hr.1 gap_14033 hl.2
    (by norm_num) upper_reach_14029

theorem upper_reach_14051 : UpperReach 14051 139150360931648 := by
  have hr := row_14051
  have hl := log_bounds hr.1
    (by change logScale (14051 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14033) (H := 139054856443140) (u := 95504488432)
    (by norm_num) (by norm_num) hr.1 gap_14051 hl.2
    (by norm_num) upper_reach_14033

theorem upper_reach_14057 : UpperReach 14057 139245869689403 := by
  have hr := row_14057
  have hl := log_bounds hr.1
    (by change logScale (14057 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14051) (H := 139150360931648) (u := 95508757679)
    (by norm_num) (by norm_num) hr.1 gap_14057 hl.2
    (by norm_num) upper_reach_14051

theorem upper_reach_14071 : UpperReach 14071 139341388401653 := by
  have hr := row_14071
  have hl := log_bounds hr.1
    (by change logScale (14071 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14057) (H := 139245869689403) (u := 95518712174)
    (by norm_num) (by norm_num) hr.1 gap_14071 hl.2
    (by norm_num) upper_reach_14057

theorem upper_reach_14081 : UpperReach 14081 139436914218194 := by
  have hr := row_14081
  have hl := log_bounds hr.1
    (by change logScale (14081 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14071) (H := 139341388401653) (u := 95525816465)
    (by norm_num) (by norm_num) hr.1 gap_14081 hl.2
    (by norm_num) upper_reach_14071

theorem upper_reach_14083 : UpperReach 14083 139532441454988 := by
  have hr := row_14083
  have hl := log_bounds hr.1
    (by change logScale (14083 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14081) (H := 139436914218194) (u := 95527236718)
    (by norm_num) (by norm_num) hr.1 gap_14083 hl.2
    (by norm_num) upper_reach_14081

theorem upper_reach_14087 : UpperReach 14087 139627971531682 := by
  have hr := row_14087
  have hl := log_bounds hr.1
    (by change logScale (14087 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14083) (H := 139532441454988) (u := 95530076618)
    (by norm_num) (by norm_num) hr.1 gap_14087 hl.2
    (by norm_num) upper_reach_14083

theorem upper_reach_14107 : UpperReach 14107 139723515795794 := by
  have hr := row_14107
  have hl := log_bounds hr.1
    (by change logScale (14107 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14087) (H := 139627971531682) (u := 95544264036)
    (by norm_num) (by norm_num) hr.1 gap_14107 hl.2
    (by norm_num) upper_reach_14087

theorem upper_reach_14143 : UpperReach 14143 139819085546646 := by
  have hr := row_14143
  have hl := log_bounds hr.1
    (by change logScale (14143 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14107) (H := 139723515795794) (u := 95569750776)
    (by norm_num) (by norm_num) hr.1 gap_14143 hl.2
    (by norm_num) upper_reach_14107

theorem upper_reach_14149 : UpperReach 14149 139914659538980 := by
  have hr := row_14149
  have hl := log_bounds hr.1
    (by change logScale (14149 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14143) (H := 139819085546646) (u := 95573992258)
    (by norm_num) (by norm_num) hr.1 gap_14149 hl.2
    (by norm_num) upper_reach_14143

theorem upper_reach_14153 : UpperReach 14153 140010236357969 := by
  have hr := row_14153
  have hl := log_bounds hr.1
    (by change logScale (14153 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14149) (H := 139914659538980) (u := 95576818913)
    (by norm_num) (by norm_num) hr.1 gap_14153 hl.2
    (by norm_num) upper_reach_14149

theorem upper_reach_14159 : UpperReach 14159 140105817415444 := by
  have hr := row_14159
  have hl := log_bounds hr.1
    (by change logScale (14159 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14153) (H := 140010236357969) (u := 95581057399)
    (by norm_num) (by norm_num) hr.1 gap_14159 hl.2
    (by norm_num) upper_reach_14153

theorem upper_reach_14173 : UpperReach 14173 140201408355737 := by
  have hr := row_14173
  have hl := log_bounds hr.1
    (by change logScale (14173 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14159) (H := 140105817415444) (u := 95590940217)
    (by norm_num) (by norm_num) hr.1 gap_14173 hl.2
    (by norm_num) upper_reach_14159

#print axioms upper_reach_14173

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
