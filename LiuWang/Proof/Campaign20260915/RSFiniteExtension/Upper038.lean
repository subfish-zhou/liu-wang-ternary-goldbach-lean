import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper037
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block038

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_8999 : UpperReach 8999 88703750048863 := by
  have hr := row_8999
  have hl := log_bounds hr.1
    (by change logScale (8999 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8971) (H := 88612701361431) (u := 91048687356)
    (by norm_num) (by norm_num) hr.1 gap_8999 hl.2
    (by norm_num) upper_reach_8971

theorem upper_reach_9001 : UpperReach 9001 88794800958517 := by
  have hr := row_9001
  have hl := log_bounds hr.1
    (by change logScale (9001 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8999) (H := 88703750048863) (u := 91050909578)
    (by norm_num) (by norm_num) hr.1 gap_9001 hl.2
    (by norm_num) upper_reach_8999

theorem upper_reach_9007 : UpperReach 9007 88885858531877 := by
  have hr := row_9007
  have hl := log_bounds hr.1
    (by change logScale (9007 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9001) (H := 88794800958517) (u := 91057573284)
    (by norm_num) (by norm_num) hr.1 gap_9007 hl.2
    (by norm_num) upper_reach_9001

theorem upper_reach_9011 : UpperReach 9011 88976920545241 := by
  have hr := row_9011
  have hl := log_bounds hr.1
    (by change logScale (9011 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9007) (H := 88885858531877) (u := 91062013288)
    (by norm_num) (by norm_num) hr.1 gap_9011 hl.2
    (by norm_num) upper_reach_9007

theorem upper_reach_9013 : UpperReach 9013 89067984777868 := by
  have hr := row_9013
  have hl := log_bounds hr.1
    (by change logScale (9013 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9011) (H := 88976920545241) (u := 91064232551)
    (by norm_num) (by norm_num) hr.1 gap_9013 hl.2
    (by norm_num) upper_reach_9011

theorem upper_reach_9029 : UpperReach 9029 89159066746893 := by
  have hr := row_9029
  have hl := log_bounds hr.1
    (by change logScale (9029 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9013) (H := 89067984777868) (u := 91081968949)
    (by norm_num) (by norm_num) hr.1 gap_9029 hl.2
    (by norm_num) upper_reach_9013

theorem upper_reach_9041 : UpperReach 9041 89250161997602 := by
  have hr := row_9041
  have hl := log_bounds hr.1
    (by change logScale (9041 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9029) (H := 89159066746893) (u := 91095250633)
    (by norm_num) (by norm_num) hr.1 gap_9041 hl.2
    (by norm_num) upper_reach_9029

theorem upper_reach_9043 : UpperReach 9043 89341259460211 := by
  have hr := row_9043
  have hl := log_bounds hr.1
    (by change logScale (9043 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9041) (H := 89250161997602) (u := 91097462533)
    (by norm_num) (by norm_num) hr.1 gap_9043 hl.2
    (by norm_num) upper_reach_9041

theorem upper_reach_9049 : UpperReach 9049 89432363555586 := by
  have hr := row_9049
  have hl := log_bounds hr.1
    (by change logScale (9049 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9043) (H := 89341259460211) (u := 91104095299)
    (by norm_num) (by norm_num) hr.1 gap_9049 hl.2
    (by norm_num) upper_reach_9043

theorem upper_reach_9059 : UpperReach 9059 89523478695804 := by
  have hr := row_9059
  have hl := log_bounds hr.1
    (by change logScale (9059 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9049) (H := 89432363555586) (u := 91115140142)
    (by norm_num) (by norm_num) hr.1 gap_9059 hl.2
    (by norm_num) upper_reach_9049

theorem upper_reach_9067 : UpperReach 9067 89614602663122 := by
  have hr := row_9067
  have hl := log_bounds hr.1
    (by change logScale (9067 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9059) (H := 89523478695804) (u := 91123967242)
    (by norm_num) (by norm_num) hr.1 gap_9067 hl.2
    (by norm_num) upper_reach_9059

theorem upper_reach_9091 : UpperReach 9091 89705753065085 := by
  have hr := row_9091
  have hl := log_bounds hr.1
    (by change logScale (9091 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9067) (H := 89614602663122) (u := 91150401887)
    (by norm_num) (by norm_num) hr.1 gap_9091 hl.2
    (by norm_num) upper_reach_9067

theorem upper_reach_9103 : UpperReach 9103 89796916658212 := by
  have hr := row_9103
  have hl := log_bounds hr.1
    (by change logScale (9103 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9091) (H := 89705753065085) (u := 91163593051)
    (by norm_num) (by norm_num) hr.1 gap_9103 hl.2
    (by norm_num) upper_reach_9091

theorem upper_reach_9109 : UpperReach 9109 89888086840401 := by
  have hr := row_9109
  have hl := log_bounds hr.1
    (by change logScale (9109 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9103) (H := 89796916658212) (u := 91170182113)
    (by norm_num) (by norm_num) hr.1 gap_9109 hl.2
    (by norm_num) upper_reach_9103

theorem upper_reach_9127 : UpperReach 9127 89979276763768 := by
  have hr := row_9127
  have hl := log_bounds hr.1
    (by change logScale (9127 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9109) (H := 89888086840401) (u := 91189923291)
    (by norm_num) (by norm_num) hr.1 gap_9127 hl.2
    (by norm_num) upper_reach_9109

theorem upper_reach_9133 : UpperReach 9133 90070473258877 := by
  have hr := row_9133
  have hl := log_bounds hr.1
    (by change logScale (9133 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9127) (H := 89979276763768) (u := 91196495033)
    (by norm_num) (by norm_num) hr.1 gap_9133 hl.2
    (by norm_num) upper_reach_9127

theorem upper_reach_9137 : UpperReach 9137 90161674132749 := by
  have hr := row_9137
  have hl := log_bounds hr.1
    (by change logScale (9137 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9133) (H := 90070473258877) (u := 91200873796)
    (by norm_num) (by norm_num) hr.1 gap_9137 hl.2
    (by norm_num) upper_reach_9133

theorem upper_reach_9151 : UpperReach 9151 90252890317210 := by
  have hr := row_9151
  have hl := log_bounds hr.1
    (by change logScale (9151 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9137) (H := 90161674132749) (u := 91216184385)
    (by norm_num) (by norm_num) hr.1 gap_9151 hl.2
    (by norm_num) upper_reach_9137

theorem upper_reach_9157 : UpperReach 9157 90344113056183 := by
  have hr := row_9157
  have hl := log_bounds hr.1
    (by change logScale (9157 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9151) (H := 90252890317210) (u := 91222738897)
    (by norm_num) (by norm_num) hr.1 gap_9157 hl.2
    (by norm_num) upper_reach_9151

theorem upper_reach_9161 : UpperReach 9161 90435340162445 := by
  have hr := row_9161
  have hl := log_bounds hr.1
    (by change logScale (9161 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9157) (H := 90344113056183) (u := 91227106186)
    (by norm_num) (by norm_num) hr.1 gap_9161 hl.2
    (by norm_num) upper_reach_9157

theorem upper_reach_9173 : UpperReach 9173 90526580359142 := by
  have hr := row_9173
  have hl := log_bounds hr.1
    (by change logScale (9173 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9161) (H := 90435340162445) (u := 91240196621)
    (by norm_num) (by norm_num) hr.1 gap_9173 hl.2
    (by norm_num) upper_reach_9161

theorem upper_reach_9181 : UpperReach 9181 90617829273285 := by
  have hr := row_9181
  have hl := log_bounds hr.1
    (by change logScale (9181 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9173) (H := 90526580359142) (u := 91248914067)
    (by norm_num) (by norm_num) hr.1 gap_9181 hl.2
    (by norm_num) upper_reach_9173

theorem upper_reach_9187 : UpperReach 9187 90709084720529 := by
  have hr := row_9187
  have hl := log_bounds hr.1
    (by change logScale (9187 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9181) (H := 90617829273285) (u := 91255447168)
    (by norm_num) (by norm_num) hr.1 gap_9187 hl.2
    (by norm_num) upper_reach_9181

theorem upper_reach_9199 : UpperReach 9199 90800353221185 := by
  have hr := row_9199
  have hl := log_bounds hr.1
    (by change logScale (9199 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9187) (H := 90709084720529) (u := 91268500580)
    (by norm_num) (by norm_num) hr.1 gap_9199 hl.2
    (by norm_num) upper_reach_9187

#print axioms upper_reach_9199

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
