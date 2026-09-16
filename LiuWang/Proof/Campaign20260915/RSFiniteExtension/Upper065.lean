import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper064
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block065

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_15107 : UpperReach 15107 149506125766809 := by
  have hr := row_15107
  have hl := log_bounds hr.1
    (by change logScale (15107 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15101) (H := 149409896631852) (u := 96229134881)
    (by norm_num) (by norm_num) hr.1 gap_15107 hl.2
    (by norm_num) upper_reach_15101

theorem upper_reach_15121 : UpperReach 15121 149602364164702 := by
  have hr := row_15121
  have hl := log_bounds hr.1
    (by change logScale (15121 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15107) (H := 149506125766809) (u := 96238397817)
    (by norm_num) (by norm_num) hr.1 gap_15121 hl.2
    (by norm_num) upper_reach_15107

theorem upper_reach_15131 : UpperReach 15131 149698609173728 := by
  have hr := row_15131
  have hl := log_bounds hr.1
    (by change logScale (15131 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15121) (H := 149602364164702) (u := 96245008950)
    (by norm_num) (by norm_num) hr.1 gap_15131 hl.2
    (by norm_num) upper_reach_15121

theorem upper_reach_15137 : UpperReach 15137 149794858147337 := by
  have hr := row_15137
  have hl := log_bounds hr.1
    (by change logScale (15137 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15131) (H := 149698609173728) (u := 96248973533)
    (by norm_num) (by norm_num) hr.1 gap_15137 hl.2
    (by norm_num) upper_reach_15131

theorem upper_reach_15139 : UpperReach 15139 149891108442125 := by
  have hr := row_15139
  have hl := log_bounds hr.1
    (by change logScale (15139 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15137) (H := 149794858147337) (u := 96250294712)
    (by norm_num) (by norm_num) hr.1 gap_15139 hl.2
    (by norm_num) upper_reach_15137

theorem upper_reach_15149 : UpperReach 15149 149987365340188 := by
  have hr := row_15149
  have hl := log_bounds hr.1
    (by change logScale (15149 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15139) (H := 149891108442125) (u := 96256897987)
    (by norm_num) (by norm_num) hr.1 gap_15149 hl.2
    (by norm_num) upper_reach_15139

theorem upper_reach_15161 : UpperReach 15161 150083630156431 := by
  have hr := row_15161
  have hl := log_bounds hr.1
    (by change logScale (15161 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15149) (H := 149987365340188) (u := 96264816167)
    (by norm_num) (by norm_num) hr.1 gap_15161 hl.2
    (by norm_num) upper_reach_15149

theorem upper_reach_15173 : UpperReach 15173 150179902884588 := by
  have hr := row_15173
  have hl := log_bounds hr.1
    (by change logScale (15173 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15161) (H := 150083630156431) (u := 96272728081)
    (by norm_num) (by norm_num) hr.1 gap_15173 hl.2
    (by norm_num) upper_reach_15161

theorem upper_reach_15187 : UpperReach 15187 150276184835407 := by
  have hr := row_15187
  have hl := log_bounds hr.1
    (by change logScale (15187 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15173) (H := 150179902884588) (u := 96281950743)
    (by norm_num) (by norm_num) hr.1 gap_15187 hl.2
    (by norm_num) upper_reach_15173

theorem upper_reach_15193 : UpperReach 15193 150372470736193 := by
  have hr := row_15193
  have hl := log_bounds hr.1
    (by change logScale (15193 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15187) (H := 150276184835407) (u := 96285900710)
    (by norm_num) (by norm_num) hr.1 gap_15193 hl.2
    (by norm_num) upper_reach_15187

theorem upper_reach_15199 : UpperReach 15199 150468760585387 := by
  have hr := row_15199
  have hl := log_bounds hr.1
    (by change logScale (15199 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15193) (H := 150372470736193) (u := 96289849118)
    (by norm_num) (by norm_num) hr.1 gap_15199 hl.2
    (by norm_num) upper_reach_15193

theorem upper_reach_15217 : UpperReach 15217 150565062270458 := by
  have hr := row_15217
  have hl := log_bounds hr.1
    (by change logScale (15217 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15199) (H := 150468760585387) (u := 96301684995)
    (by norm_num) (by norm_num) hr.1 gap_15217 hl.2
    (by norm_num) upper_reach_15199

theorem upper_reach_15227 : UpperReach 15227 150661370524968 := by
  have hr := row_15227
  have hl := log_bounds hr.1
    (by change logScale (15227 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15217) (H := 150565062270458) (u := 96308254434)
    (by norm_num) (by norm_num) hr.1 gap_15227 hl.2
    (by norm_num) upper_reach_15217

theorem upper_reach_15233 : UpperReach 15233 150757682719071 := by
  have hr := row_15233
  have hl := log_bounds hr.1
    (by change logScale (15233 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15227) (H := 150661370524968) (u := 96312194027)
    (by norm_num) (by norm_num) hr.1 gap_15233 hl.2
    (by norm_num) upper_reach_15227

theorem upper_reach_15241 : UpperReach 15241 150854000163552 := by
  have hr := row_15241
  have hl := log_bounds hr.1
    (by change logScale (15241 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15233) (H := 150757682719071) (u := 96317444405)
    (by norm_num) (by norm_num) hr.1 gap_15241 hl.2
    (by norm_num) upper_reach_15233

theorem upper_reach_15259 : UpperReach 15259 150950329411313 := by
  have hr := row_15259
  have hl := log_bounds hr.1
    (by change logScale (15259 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15241) (H := 150854000163552) (u := 96329247685)
    (by norm_num) (by norm_num) hr.1 gap_15259 hl.2
    (by norm_num) upper_reach_15241

theorem upper_reach_15263 : UpperReach 15263 151046661280134 := by
  have hr := row_15263
  have hl := log_bounds hr.1
    (by change logScale (15263 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15259) (H := 150950329411313) (u := 96331868745)
    (by norm_num) (by norm_num) hr.1 gap_15263 hl.2
    (by norm_num) upper_reach_15259

theorem upper_reach_15269 : UpperReach 15269 151142997079258 := by
  have hr := row_15269
  have hl := log_bounds hr.1
    (by change logScale (15269 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15263) (H := 151046661280134) (u := 96335799048)
    (by norm_num) (by norm_num) hr.1 gap_15269 hl.2
    (by norm_num) upper_reach_15263

theorem upper_reach_15271 : UpperReach 15271 151239334188139 := by
  have hr := row_15271
  have hl := log_bounds hr.1
    (by change logScale (15271 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15269) (H := 151142997079258) (u := 96337108805)
    (by norm_num) (by norm_num) hr.1 gap_15271 hl.2
    (by norm_num) upper_reach_15269

theorem upper_reach_15277 : UpperReach 15277 151335675225264 := by
  have hr := row_15277
  have hl := log_bounds hr.1
    (by change logScale (15277 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15271) (H := 151239334188139) (u := 96341037049)
    (by norm_num) (by norm_num) hr.1 gap_15277 hl.2
    (by norm_num) upper_reach_15271

theorem upper_reach_15287 : UpperReach 15287 151432022806036 := by
  have hr := row_15287
  have hl := log_bounds hr.1
    (by change logScale (15287 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15277) (H := 151335675225264) (u := 96347580696)
    (by norm_num) (by norm_num) hr.1 gap_15287 hl.2
    (by norm_num) upper_reach_15277

theorem upper_reach_15289 : UpperReach 15289 151528371695023 := by
  have hr := row_15289
  have hl := log_bounds hr.1
    (by change logScale (15289 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15287) (H := 151432022806036) (u := 96348888911)
    (by norm_num) (by norm_num) hr.1 gap_15289 hl.2
    (by norm_num) upper_reach_15287

theorem upper_reach_15299 : UpperReach 15299 151624727122522 := by
  have hr := row_15299
  have hl := log_bounds hr.1
    (by change logScale (15299 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15289) (H := 151528371695023) (u := 96355427423)
    (by norm_num) (by norm_num) hr.1 gap_15299 hl.2
    (by norm_num) upper_reach_15289

theorem upper_reach_15307 : UpperReach 15307 151721087777755 := by
  have hr := row_15307
  have hl := log_bounds hr.1
    (by change logScale (15307 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15299) (H := 151624727122522) (u := 96360655157)
    (by norm_num) (by norm_num) hr.1 gap_15307 hl.2
    (by norm_num) upper_reach_15299

#print axioms upper_reach_15307

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
