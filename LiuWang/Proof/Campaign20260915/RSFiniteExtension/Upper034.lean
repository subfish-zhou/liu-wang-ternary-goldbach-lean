import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper033
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block034

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_8117 : UpperReach 8117 80010875321213 := by
  have hr := row_8117
  have hl := log_bounds hr.1
    (by change logScale (8117 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8111) (H := 79920858162101) (u := 90017159036)
    (by norm_num) (by norm_num) hr.1 gap_8117 hl.2
    (by norm_num) upper_reach_8111

theorem upper_reach_8123 : UpperReach 8123 80100899869488 := by
  have hr := row_8123
  have hl := log_bounds hr.1
    (by change logScale (8123 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8117) (H := 80010875321213) (u := 90024548199)
    (by norm_num) (by norm_num) hr.1 gap_8123 hl.2
    (by norm_num) upper_reach_8117

theorem upper_reach_8147 : UpperReach 8147 80190953919935 := by
  have hr := row_8147
  have hl := log_bounds hr.1
    (by change logScale (8147 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8123) (H := 80100899869488) (u := 90054050371)
    (by norm_num) (by norm_num) hr.1 gap_8147 hl.2
    (by norm_num) upper_reach_8123

theorem upper_reach_8161 : UpperReach 8161 80281025139874 := by
  have hr := row_8161
  have hl := log_bounds hr.1
    (by change logScale (8161 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8147) (H := 80190953919935) (u := 90071219863)
    (by norm_num) (by norm_num) hr.1 gap_8161 hl.2
    (by norm_num) upper_reach_8147

theorem upper_reach_8167 : UpperReach 8167 80371103709152 := by
  have hr := row_8167
  have hl := log_bounds hr.1
    (by change logScale (8167 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8161) (H := 80281025139874) (u := 90078569202)
    (by norm_num) (by norm_num) hr.1 gap_8167 hl.2
    (by norm_num) upper_reach_8161

theorem upper_reach_8171 : UpperReach 8171 80461187174990 := by
  have hr := row_8171
  have hl := log_bounds hr.1
    (by change logScale (8171 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8167) (H := 80371103709152) (u := 90083465762)
    (by norm_num) (by norm_num) hr.1 gap_8171 hl.2
    (by norm_num) upper_reach_8167

theorem upper_reach_8179 : UpperReach 8179 80551280426762 := by
  have hr := row_8179
  have hl := log_bounds hr.1
    (by change logScale (8179 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8171) (H := 80461187174990) (u := 90093251696)
    (by norm_num) (by norm_num) hr.1 gap_8179 hl.2
    (by norm_num) upper_reach_8171

theorem upper_reach_8191 : UpperReach 8191 80641388339501 := by
  have hr := row_8191
  have hl := log_bounds hr.1
    (by change logScale (8191 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8179) (H := 80551280426762) (u := 90107912663)
    (by norm_num) (by norm_num) hr.1 gap_8191 hl.2
    (by norm_num) upper_reach_8179

theorem upper_reach_8209 : UpperReach 8209 80731518203466 := by
  have hr := row_8209
  have hl := log_bounds hr.1
    (by change logScale (8209 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8191) (H := 80641388339501) (u := 90129863889)
    (by norm_num) (by norm_num) hr.1 gap_8209 hl.2
    (by norm_num) upper_reach_8191

theorem upper_reach_8219 : UpperReach 8219 80821660241769 := by
  have hr := row_8219
  have hl := log_bounds hr.1
    (by change logScale (8219 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8209) (H := 80731518203466) (u := 90142038227)
    (by norm_num) (by norm_num) hr.1 gap_8219 hl.2
    (by norm_num) upper_reach_8209

theorem upper_reach_8221 : UpperReach 8221 80911804713162 := by
  have hr := row_8221
  have hl := log_bounds hr.1
    (by change logScale (8221 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8219) (H := 80821660241769) (u := 90144471317)
    (by norm_num) (by norm_num) hr.1 gap_8221 hl.2
    (by norm_num) upper_reach_8219

theorem upper_reach_8231 : UpperReach 8231 81001961341133 := by
  have hr := row_8231
  have hl := log_bounds hr.1
    (by change logScale (8231 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8221) (H := 80911804713162) (u := 90156627895)
    (by norm_num) (by norm_num) hr.1 gap_8231 hl.2
    (by norm_num) upper_reach_8221

theorem upper_reach_8233 : UpperReach 8233 81092120398648 := by
  have hr := row_8233
  have hl := log_bounds hr.1
    (by change logScale (8233 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8231) (H := 81001961341133) (u := 90159057439)
    (by norm_num) (by norm_num) hr.1 gap_8233 hl.2
    (by norm_num) upper_reach_8231

theorem upper_reach_8237 : UpperReach 8237 81182284313479 := by
  have hr := row_8237
  have hl := log_bounds hr.1
    (by change logScale (8237 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8233) (H := 81092120398648) (u := 90163914755)
    (by norm_num) (by norm_num) hr.1 gap_8237 hl.2
    (by norm_num) upper_reach_8233

theorem upper_reach_8243 : UpperReach 8243 81272455509864 := by
  have hr := row_8243
  have hl := log_bounds hr.1
    (by change logScale (8243 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8237) (H := 81182284313479) (u := 90171196309)
    (by norm_num) (by norm_num) hr.1 gap_8243 hl.2
    (by norm_num) upper_reach_8237

theorem upper_reach_8263 : UpperReach 8263 81362650939873 := by
  have hr := row_8263
  have hl := log_bounds hr.1
    (by change logScale (8263 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8243) (H := 81272455509864) (u := 90195429933)
    (by norm_num) (by norm_num) hr.1 gap_8263 hl.2
    (by norm_num) upper_reach_8243

theorem upper_reach_8269 : UpperReach 8269 81452853628532 := by
  have hr := row_8269
  have hl := log_bounds hr.1
    (by change logScale (8269 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8263) (H := 81362650939873) (u := 90202688583)
    (by norm_num) (by norm_num) hr.1 gap_8269 hl.2
    (by norm_num) upper_reach_8263

theorem upper_reach_8273 : UpperReach 8273 81543061153366 := by
  have hr := row_8273
  have hl := log_bounds hr.1
    (by change logScale (8273 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8269) (H := 81452853628532) (u := 90207524758)
    (by norm_num) (by norm_num) hr.1 gap_8273 hl.2
    (by norm_num) upper_reach_8269

theorem upper_reach_8287 : UpperReach 8287 81633285586416 := by
  have hr := row_8287
  have hl := log_bounds hr.1
    (by change logScale (8287 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8273) (H := 81543061153366) (u := 90224432974)
    (by norm_num) (by norm_num) hr.1 gap_8287 hl.2
    (by norm_num) upper_reach_8273

theorem upper_reach_8291 : UpperReach 8291 81723514845139 := by
  have hr := row_8291
  have hl := log_bounds hr.1
    (by change logScale (8291 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8287) (H := 81633285586416) (u := 90229258647)
    (by norm_num) (by norm_num) hr.1 gap_8291 hl.2
    (by norm_num) upper_reach_8287

theorem upper_reach_8293 : UpperReach 8293 81813746515825 := by
  have hr := row_8293
  have hl := log_bounds hr.1
    (by change logScale (8293 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8291) (H := 81723514845139) (u := 90231670610)
    (by norm_num) (by norm_num) hr.1 gap_8293 hl.2
    (by norm_num) upper_reach_8291

theorem upper_reach_8297 : UpperReach 8297 81903983008693 := by
  have hr := row_8297
  have hl := log_bounds hr.1
    (by change logScale (8297 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8293) (H := 81813746515825) (u := 90236492792)
    (by norm_num) (by norm_num) hr.1 gap_8297 hl.2
    (by norm_num) upper_reach_8293

theorem upper_reach_8311 : UpperReach 8311 81994236360910 := by
  have hr := row_8311
  have hl := log_bounds hr.1
    (by change logScale (8311 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8297) (H := 81903983008693) (u := 90253352141)
    (by norm_num) (by norm_num) hr.1 gap_8311 hl.2
    (by norm_num) upper_reach_8297

theorem upper_reach_8317 : UpperReach 8317 82084496929870 := by
  have hr := row_8317
  have hl := log_bounds hr.1
    (by change logScale (8317 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8311) (H := 81994236360910) (u := 90260568884)
    (by norm_num) (by norm_num) hr.1 gap_8317 hl.2
    (by norm_num) upper_reach_8311

#print axioms upper_reach_8317

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
