import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper055
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block056

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_13003 : UpperReach 13003 128876738283888 := by
  have hr := row_13003
  have hl := log_bounds hr.1
    (by change logScale (13003 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13001) (H := 128782008930056) (u := 94729353756)
    (by norm_num) (by norm_num) hr.1 gap_13003 hl.2
    (by norm_num) upper_reach_13001

theorem upper_reach_13007 : UpperReach 13007 128971470713460 := by
  have hr := row_13007
  have hl := log_bounds hr.1
    (by change logScale (13007 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13003) (H := 128876738283888) (u := 94732429496)
    (by norm_num) (by norm_num) hr.1 gap_13007 hl.2
    (by norm_num) upper_reach_13003

theorem upper_reach_13009 : UpperReach 13009 129066204680548 := by
  have hr := row_13009
  have hl := log_bounds hr.1
    (by change logScale (13009 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13007) (H := 128971470713460) (u := 94733967012)
    (by norm_num) (by norm_num) hr.1 gap_13009 hl.2
    (by norm_num) upper_reach_13007

theorem upper_reach_13033 : UpperReach 13033 129160957079405 := by
  have hr := row_13033
  have hl := log_bounds hr.1
    (by change logScale (13033 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13009) (H := 129066204680548) (u := 94752398781)
    (by norm_num) (by norm_num) hr.1 gap_13033 hl.2
    (by norm_num) upper_reach_13009

theorem upper_reach_13037 : UpperReach 13037 129255712546923 := by
  have hr := row_13037
  have hl := log_bounds hr.1
    (by change logScale (13037 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13033) (H := 129160957079405) (u := 94755467442)
    (by norm_num) (by norm_num) hr.1 gap_13037 hl.2
    (by norm_num) upper_reach_13033

theorem upper_reach_13043 : UpperReach 13043 129350472615668 := by
  have hr := row_13043
  have hl := log_bounds hr.1
    (by change logScale (13043 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13037) (H := 129255712546923) (u := 94760068669)
    (by norm_num) (by norm_num) hr.1 gap_13043 hl.2
    (by norm_num) upper_reach_13037

theorem upper_reach_13049 : UpperReach 13049 129445237283524 := by
  have hr := row_13049
  have hl := log_bounds hr.1
    (by change logScale (13049 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13043) (H := 129350472615668) (u := 94764667780)
    (by norm_num) (by norm_num) hr.1 gap_13049 hl.2
    (by norm_num) upper_reach_13043

theorem upper_reach_13063 : UpperReach 13063 129540012674421 := by
  have hr := row_13063
  have hl := log_bounds hr.1
    (by change logScale (13063 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13049) (H := 129445237283524) (u := 94775390821)
    (by norm_num) (by norm_num) hr.1 gap_13063 hl.2
    (by norm_num) upper_reach_13049

theorem upper_reach_13093 : UpperReach 13093 129634811004615 := by
  have hr := row_13093
  have hl := log_bounds hr.1
    (by change logScale (13093 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13063) (H := 129540012674421) (u := 94798330118)
    (by norm_num) (by norm_num) hr.1 gap_13093 hl.2
    (by norm_num) upper_reach_13063

theorem upper_reach_13099 : UpperReach 13099 129729613916361 := by
  have hr := row_13099
  have hl := log_bounds hr.1
    (by change logScale (13099 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13093) (H := 129634811004615) (u := 94802911670)
    (by norm_num) (by norm_num) hr.1 gap_13099 hl.2
    (by norm_num) upper_reach_13093

theorem upper_reach_13103 : UpperReach 13103 129824419881309 := by
  have hr := row_13103
  have hl := log_bounds hr.1
    (by change logScale (13103 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13099) (H := 129729613916361) (u := 94805964872)
    (by norm_num) (by norm_num) hr.1 gap_13103 hl.2
    (by norm_num) upper_reach_13099

theorem upper_reach_13109 : UpperReach 13109 129919230424313 := by
  have hr := row_13109
  have hl := log_bounds hr.1
    (by change logScale (13109 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13103) (H := 129824419881309) (u := 94810542928)
    (by norm_num) (by norm_num) hr.1 gap_13109 hl.2
    (by norm_num) upper_reach_13103

theorem upper_reach_13121 : UpperReach 13121 130014050117146 := by
  have hr := row_13121
  have hl := log_bounds hr.1
    (by change logScale (13121 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13109) (H := 129919230424313) (u := 94819692757)
    (by norm_num) (by norm_num) hr.1 gap_13121 hl.2
    (by norm_num) upper_reach_13109

theorem upper_reach_13127 : UpperReach 13127 130108874381756 := by
  have hr := row_13127
  have hl := log_bounds hr.1
    (by change logScale (13127 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13121) (H := 130014050117146) (u := 94824264534)
    (by norm_num) (by norm_num) hr.1 gap_13127 hl.2
    (by norm_num) upper_reach_13121

theorem upper_reach_13147 : UpperReach 13147 130203713870545 := by
  have hr := row_13147
  have hl := log_bounds hr.1
    (by change logScale (13147 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13127) (H := 130108874381756) (u := 94839488713)
    (by norm_num) (by norm_num) hr.1 gap_13147 hl.2
    (by norm_num) upper_reach_13127

theorem upper_reach_13151 : UpperReach 13151 130298556401390 := by
  have hr := row_13151
  have hl := log_bounds hr.1
    (by change logScale (13151 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13147) (H := 130203713870545) (u := 94842530769)
    (by norm_num) (by norm_num) hr.1 gap_13151 hl.2
    (by norm_num) upper_reach_13147

theorem upper_reach_13159 : UpperReach 13159 130393405013573 := by
  have hr := row_13159
  have hl := log_bounds hr.1
    (by change logScale (13159 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13151) (H := 130298556401390) (u := 94848612107)
    (by norm_num) (by norm_num) hr.1 gap_13159 hl.2
    (by norm_num) upper_reach_13151

theorem upper_reach_13163 : UpperReach 13163 130488256665039 := by
  have hr := row_13163
  have hl := log_bounds hr.1
    (by change logScale (13163 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13159) (H := 130393405013573) (u := 94851651390)
    (by norm_num) (by norm_num) hr.1 gap_13163 hl.2
    (by norm_num) upper_reach_13159

theorem upper_reach_13171 : UpperReach 13171 130583114392301 := by
  have hr := row_13171
  have hl := log_bounds hr.1
    (by change logScale (13171 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13163) (H := 130488256665039) (u := 94857727186)
    (by norm_num) (by norm_num) hr.1 gap_13171 hl.2
    (by norm_num) upper_reach_13163

theorem upper_reach_13177 : UpperReach 13177 130677976673988 := by
  have hr := row_13177
  have hl := log_bounds hr.1
    (by change logScale (13177 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13171) (H := 130583114392301) (u := 94862281611)
    (by norm_num) (by norm_num) hr.1 gap_13177 hl.2
    (by norm_num) upper_reach_13171

theorem upper_reach_13183 : UpperReach 13183 130772843508027 := by
  have hr := row_13183
  have hl := log_bounds hr.1
    (by change logScale (13183 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13177) (H := 130677976673988) (u := 94866833963)
    (by norm_num) (by norm_num) hr.1 gap_13183 hl.2
    (by norm_num) upper_reach_13177

theorem upper_reach_13187 : UpperReach 13187 130867713375817 := by
  have hr := row_13187
  have hl := log_bounds hr.1
    (by change logScale (13187 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13183) (H := 130772843508027) (u := 94869867714)
    (by norm_num) (by norm_num) hr.1 gap_13187 hl.2
    (by norm_num) upper_reach_13183

theorem upper_reach_13217 : UpperReach 13217 130962605967446 := by
  have hr := row_13217
  have hl := log_bounds hr.1
    (by change logScale (13217 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13187) (H := 130867713375817) (u := 94892591553)
    (by norm_num) (by norm_num) hr.1 gap_13217 hl.2
    (by norm_num) upper_reach_13187

theorem upper_reach_13219 : UpperReach 13219 131057500072164 := by
  have hr := row_13219
  have hl := log_bounds hr.1
    (by change logScale (13219 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13217) (H := 130962605967446) (u := 94894104642)
    (by norm_num) (by norm_num) hr.1 gap_13219 hl.2
    (by norm_num) upper_reach_13217

#print axioms upper_reach_13219

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
