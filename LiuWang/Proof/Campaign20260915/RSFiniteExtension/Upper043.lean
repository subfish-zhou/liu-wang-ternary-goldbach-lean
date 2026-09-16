import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper042
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block043

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_10079 : UpperReach 10079 99697108041862 := by
  have hr := row_10079
  have hl := log_bounds hr.1
    (by change logScale (10079 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10069) (H := 99604925948517) (u := 92182093269)
    (by norm_num) (by norm_num) hr.1 gap_10079 hl.2
    (by norm_num) upper_reach_10069

theorem upper_reach_10091 : UpperReach 10091 99789302034068 := by
  have hr := row_10091
  have hl := log_bounds hr.1
    (by change logScale (10091 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10079) (H := 99697108041862) (u := 92193992130)
    (by norm_num) (by norm_num) hr.1 gap_10091 hl.2
    (by norm_num) upper_reach_10079

theorem upper_reach_10093 : UpperReach 10093 99881498008042 := by
  have hr := row_10093
  have hl := log_bounds hr.1
    (by change logScale (10093 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10091) (H := 99789302034068) (u := 92195973898)
    (by norm_num) (by norm_num) hr.1 gap_10093 hl.2
    (by norm_num) upper_reach_10091

theorem upper_reach_10099 : UpperReach 10099 99973699924964 := by
  have hr := row_10099
  have hl := log_bounds hr.1
    (by change logScale (10099 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10093) (H := 99881498008042) (u := 92201916846)
    (by norm_num) (by norm_num) hr.1 gap_10099 hl.2
    (by norm_num) upper_reach_10093

theorem upper_reach_10103 : UpperReach 10103 100065905801890 := by
  have hr := row_10103
  have hl := log_bounds hr.1
    (by change logScale (10103 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10099) (H := 99973699924964) (u := 92205876850)
    (by norm_num) (by norm_num) hr.1 gap_10103 hl.2
    (by norm_num) upper_reach_10099

theorem upper_reach_10111 : UpperReach 10111 100158119594123 := by
  have hr := row_10111
  have hl := log_bounds hr.1
    (by change logScale (10111 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10103) (H := 100065905801890) (u := 92213792157)
    (by norm_num) (by norm_num) hr.1 gap_10111 hl.2
    (by norm_num) upper_reach_10103

theorem upper_reach_10133 : UpperReach 10133 100250355121199 := by
  have hr := row_10133
  have hl := log_bounds hr.1
    (by change logScale (10133 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10111) (H := 100158119594123) (u := 92235527000)
    (by norm_num) (by norm_num) hr.1 gap_10133 hl.2
    (by norm_num) upper_reach_10111

theorem upper_reach_10139 : UpperReach 10139 100342596567770 := by
  have hr := row_10139
  have hl := log_bounds hr.1
    (by change logScale (10139 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10133) (H := 100250355121199) (u := 92241446495)
    (by norm_num) (by norm_num) hr.1 gap_10139 hl.2
    (by norm_num) upper_reach_10133

theorem upper_reach_10141 : UpperReach 10141 100434839986728 := by
  have hr := row_10141
  have hl := log_bounds hr.1
    (by change logScale (10141 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10139) (H := 100342596567770) (u := 92243418882)
    (by norm_num) (by norm_num) hr.1 gap_10141 hl.2
    (by norm_num) upper_reach_10139

theorem upper_reach_10151 : UpperReach 10151 100527093261788 := by
  have hr := row_10151
  have hl := log_bounds hr.1
    (by change logScale (10151 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10141) (H := 100434839986728) (u := 92253274984)
    (by norm_num) (by norm_num) hr.1 gap_10151 hl.2
    (by norm_num) upper_reach_10141

theorem upper_reach_10159 : UpperReach 10159 100619354414741 := by
  have hr := row_10159
  have hl := log_bounds hr.1
    (by change logScale (10159 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10151) (H := 100527093261788) (u := 92261152877)
    (by norm_num) (by norm_num) hr.1 gap_10159 hl.2
    (by norm_num) upper_reach_10151

theorem upper_reach_10163 : UpperReach 10163 100711619504314 := by
  have hr := row_10163
  have hl := log_bounds hr.1
    (by change logScale (10163 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10159) (H := 100619354414741) (u := 92265089497)
    (by norm_num) (by norm_num) hr.1 gap_10163 hl.2
    (by norm_num) upper_reach_10159

theorem upper_reach_10169 : UpperReach 10169 100803890495914 := by
  have hr := row_10169
  have hl := log_bounds hr.1
    (by change logScale (10169 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10163) (H := 100711619504314) (u := 92270991524)
    (by norm_num) (by norm_num) hr.1 gap_10169 hl.2
    (by norm_num) upper_reach_10163

theorem upper_reach_10177 : UpperReach 10177 100896169351468 := by
  have hr := row_10177
  have hl := log_bounds hr.1
    (by change logScale (10177 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10169) (H := 100803890495914) (u := 92278855478)
    (by norm_num) (by norm_num) hr.1 gap_10177 hl.2
    (by norm_num) upper_reach_10169

theorem upper_reach_10181 : UpperReach 10181 100988452136681 := by
  have hr := row_10181
  have hl := log_bounds hr.1
    (by change logScale (10181 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10177) (H := 100896169351468) (u := 92282785137)
    (by norm_num) (by norm_num) hr.1 gap_10181 hl.2
    (by norm_num) upper_reach_10177

theorem upper_reach_10193 : UpperReach 10193 101080746701614 := by
  have hr := row_10193
  have hl := log_bounds hr.1
    (by change logScale (10193 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10181) (H := 100988452136681) (u := 92294564857)
    (by norm_num) (by norm_num) hr.1 gap_10193 hl.2
    (by norm_num) upper_reach_10181

theorem upper_reach_10211 : UpperReach 10211 101173058910151 := by
  have hr := row_10211
  have hl := log_bounds hr.1
    (by change logScale (10211 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10193) (H := 101080746701614) (u := 92312208461)
    (by norm_num) (by norm_num) hr.1 gap_10211 hl.2
    (by norm_num) upper_reach_10193

theorem upper_reach_10223 : UpperReach 10223 101265382863820 := by
  have hr := row_10223
  have hl := log_bounds hr.1
    (by change logScale (10223 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10211) (H := 101173058910151) (u := 92323953593)
    (by norm_num) (by norm_num) hr.1 gap_10223 hl.2
    (by norm_num) upper_reach_10211

theorem upper_reach_10243 : UpperReach 10243 101357726362106 := by
  have hr := row_10243
  have hl := log_bounds hr.1
    (by change logScale (10243 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10223) (H := 101265382863820) (u := 92343498210)
    (by norm_num) (by norm_num) hr.1 gap_10243 hl.2
    (by norm_num) upper_reach_10223

theorem upper_reach_10247 : UpperReach 10247 101450073764736 := by
  have hr := row_10247
  have hl := log_bounds hr.1
    (by change logScale (10247 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10243) (H := 101357726362106) (u := 92347402554)
    (by norm_num) (by norm_num) hr.1 gap_10247 hl.2
    (by norm_num) upper_reach_10243

theorem upper_reach_10253 : UpperReach 10253 101542427021024 := by
  have hr := row_10253
  have hl := log_bounds hr.1
    (by change logScale (10253 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10247) (H := 101450073764736) (u := 92353256212)
    (by norm_num) (by norm_num) hr.1 gap_10253 hl.2
    (by norm_num) upper_reach_10247

theorem upper_reach_10259 : UpperReach 10259 101634786127547 := by
  have hr := row_10259
  have hl := log_bounds hr.1
    (by change logScale (10259 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10253) (H := 101542427021024) (u := 92359106447)
    (by norm_num) (by norm_num) hr.1 gap_10259 hl.2
    (by norm_num) upper_reach_10253

theorem upper_reach_10267 : UpperReach 10267 101727153029062 := by
  have hr := row_10267
  have hl := log_bounds hr.1
    (by change logScale (10267 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10259) (H := 101634786127547) (u := 92366901439)
    (by norm_num) (by norm_num) hr.1 gap_10267 hl.2
    (by norm_num) upper_reach_10259

theorem upper_reach_10271 : UpperReach 10271 101819523825795 := by
  have hr := row_10271
  have hl := log_bounds hr.1
    (by change logScale (10271 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10267) (H := 101727153029062) (u := 92370796657)
    (by norm_num) (by norm_num) hr.1 gap_10271 hl.2
    (by norm_num) upper_reach_10267

#print axioms upper_reach_10271

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
