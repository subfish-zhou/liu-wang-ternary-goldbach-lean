import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper028
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block029

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_7001 : UpperReach 7001 69292748495138 := by
  have hr := row_7001
  have hl := log_bounds hr.1
    (by change logScale (7001 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6997) (H := 69204210412344) (u := 88538082718)
    (by norm_num) (by norm_num) hr.1 gap_7001 hl.2
    (by norm_num) upper_reach_6997

theorem upper_reach_7013 : UpperReach 7013 69381303703668 := by
  have hr := row_7013
  have hl := log_bounds hr.1
    (by change logScale (7013 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7001) (H := 69292748495138) (u := 88555208454)
    (by norm_num) (by norm_num) hr.1 gap_7013 hl.2
    (by norm_num) upper_reach_7001

theorem upper_reach_7019 : UpperReach 7019 69469867464080 := by
  have hr := row_7019
  have hl := log_bounds hr.1
    (by change logScale (7019 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7013) (H := 69381303703668) (u := 88563760336)
    (by norm_num) (by norm_num) hr.1 gap_7019 hl.2
    (by norm_num) upper_reach_7013

theorem upper_reach_7027 : UpperReach 7027 69558442615636 := by
  have hr := row_7027
  have hl := log_bounds hr.1
    (by change logScale (7027 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7019) (H := 69469867464080) (u := 88575151480)
    (by norm_num) (by norm_num) hr.1 gap_7027 hl.2
    (by norm_num) upper_reach_7019

theorem upper_reach_7039 : UpperReach 7039 69647034829616 := by
  have hr := row_7039
  have hl := log_bounds hr.1
    (by change logScale (7039 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7027) (H := 69558442615636) (u := 88592213904)
    (by norm_num) (by norm_num) hr.1 gap_7039 hl.2
    (by norm_num) upper_reach_7027

theorem upper_reach_7043 : UpperReach 7043 69735632724608 := by
  have hr := row_7043
  have hl := log_bounds hr.1
    (by change logScale (7043 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7039) (H := 69647034829616) (u := 88597894916)
    (by norm_num) (by norm_num) hr.1 gap_7043 hl.2
    (by norm_num) upper_reach_7039

theorem upper_reach_7057 : UpperReach 7057 69824250477762 := by
  have hr := row_7057
  have hl := log_bounds hr.1
    (by change logScale (7057 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7043) (H := 69735632724608) (u := 88617753078)
    (by norm_num) (by norm_num) hr.1 gap_7057 hl.2
    (by norm_num) upper_reach_7043

theorem upper_reach_7069 : UpperReach 7069 69912885220868 := by
  have hr := row_7069
  have hl := log_bounds hr.1
    (by change logScale (7069 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7057) (H := 69824250477762) (u := 88634743030)
    (by norm_num) (by norm_num) hr.1 gap_7069 hl.2
    (by norm_num) upper_reach_7057

theorem upper_reach_7079 : UpperReach 7079 70001534100250 := by
  have hr := row_7079
  have hl := log_bounds hr.1
    (by change logScale (7079 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7069) (H := 69912885220868) (u := 88648879306)
    (by norm_num) (by norm_num) hr.1 gap_7079 hl.2
    (by norm_num) upper_reach_7069

theorem upper_reach_7103 : UpperReach 7103 70090216825384 := by
  have hr := row_7103
  have hl := log_bounds hr.1
    (by change logScale (7103 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7079) (H := 70001534100250) (u := 88682725058)
    (by norm_num) (by norm_num) hr.1 gap_7103 hl.2
    (by norm_num) upper_reach_7079

theorem upper_reach_7109 : UpperReach 7109 70178907994088 := by
  have hr := row_7109
  have hl := log_bounds hr.1
    (by change logScale (7109 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7103) (H := 70090216825384) (u := 88691168628)
    (by norm_num) (by norm_num) hr.1 gap_7109 hl.2
    (by norm_num) upper_reach_7103

theorem upper_reach_7121 : UpperReach 7121 70267616028572 := by
  have hr := row_7121
  have hl := log_bounds hr.1
    (by change logScale (7121 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7109) (H := 70178907994088) (u := 88708034408)
    (by norm_num) (by norm_num) hr.1 gap_7121 hl.2
    (by norm_num) upper_reach_7109

theorem upper_reach_7127 : UpperReach 7127 70356332485291 := by
  have hr := row_7127
  have hl := log_bounds hr.1
    (by change logScale (7127 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7121) (H := 70267616028572) (u := 88716456643)
    (by norm_num) (by norm_num) hr.1 gap_7127 hl.2
    (by norm_num) upper_reach_7121

theorem upper_reach_7129 : UpperReach 7129 70445051747846 := by
  have hr := row_7129
  have hl := log_bounds hr.1
    (by change logScale (7129 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7127) (H := 70356332485291) (u := 88719262479)
    (by norm_num) (by norm_num) hr.1 gap_7129 hl.2
    (by norm_num) upper_reach_7127

theorem upper_reach_7151 : UpperReach 7151 70533801822751 := by
  have hr := row_7151
  have hl := log_bounds hr.1
    (by change logScale (7151 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7129) (H := 70445051747846) (u := 88750074829)
    (by norm_num) (by norm_num) hr.1 gap_7151 hl.2
    (by norm_num) upper_reach_7129

theorem upper_reach_7159 : UpperReach 7159 70622563078649 := by
  have hr := row_7159
  have hl := log_bounds hr.1
    (by change logScale (7159 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7151) (H := 70533801822751) (u := 88761255822)
    (by norm_num) (by norm_num) hr.1 gap_7159 hl.2
    (by norm_num) upper_reach_7151

theorem upper_reach_7177 : UpperReach 7177 70711349446168 := by
  have hr := row_7177
  have hl := log_bounds hr.1
    (by change logScale (7177 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7159) (H := 70622563078649) (u := 88786367443)
    (by norm_num) (by norm_num) hr.1 gap_7177 hl.2
    (by norm_num) upper_reach_7159

theorem upper_reach_7187 : UpperReach 7187 70800149737387 := by
  have hr := row_7187
  have hl := log_bounds hr.1
    (by change logScale (7187 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7177) (H := 70711349446168) (u := 88800291143)
    (by norm_num) (by norm_num) hr.1 gap_7187 hl.2
    (by norm_num) upper_reach_7177

theorem upper_reach_7193 : UpperReach 7193 70888958373530 := by
  have hr := row_7193
  have hl := log_bounds hr.1
    (by change logScale (7193 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7187) (H := 70800149737387) (u := 88808636067)
    (by norm_num) (by norm_num) hr.1 gap_7193 hl.2
    (by norm_num) upper_reach_7187

theorem upper_reach_7207 : UpperReach 7207 70977786454124 := by
  have hr := row_7207
  have hl := log_bounds hr.1
    (by change logScale (7207 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7193) (H := 70888958373530) (u := 88828080518)
    (by norm_num) (by norm_num) hr.1 gap_7207 hl.2
    (by norm_num) upper_reach_7193

theorem upper_reach_7211 : UpperReach 7211 71066620083337 := by
  have hr := row_7211
  have hl := log_bounds hr.1
    (by change logScale (7211 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7207) (H := 70977786454124) (u := 88833629137)
    (by norm_num) (by norm_num) hr.1 gap_7211 hl.2
    (by norm_num) upper_reach_7207

theorem upper_reach_7213 : UpperReach 7213 71155456485706 := by
  have hr := row_7213
  have hl := log_bounds hr.1
    (by change logScale (7213 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7211) (H := 71066620083337) (u := 88836402293)
    (by norm_num) (by norm_num) hr.1 gap_7213 hl.2
    (by norm_num) upper_reach_7211

theorem upper_reach_7219 : UpperReach 7219 71244301202932 := by
  have hr := row_7219
  have hl := log_bounds hr.1
    (by change logScale (7219 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7213) (H := 71155456485706) (u := 88844717150)
    (by norm_num) (by norm_num) hr.1 gap_7219 hl.2
    (by norm_num) upper_reach_7213

theorem upper_reach_7229 : UpperReach 7229 71333159762906 := by
  have hr := row_7229
  have hl := log_bounds hr.1
    (by change logScale (7229 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7219) (H := 71244301202932) (u := 88858559898)
    (by norm_num) (by norm_num) hr.1 gap_7229 hl.2
    (by norm_num) upper_reach_7219

#print axioms upper_reach_7229

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
