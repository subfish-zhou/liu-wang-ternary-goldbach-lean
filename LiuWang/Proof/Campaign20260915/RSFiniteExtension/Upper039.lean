import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper038
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block039

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_9203 : UpperReach 9203 90891626069195 := by
  have hr := row_9203
  have hl := log_bounds hr.1
    (by change logScale (9203 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9199) (H := 90800353221185) (u := 91272847934)
    (by norm_num) (by norm_num) hr.1 gap_9203 hl.2
    (by norm_num) upper_reach_9199

theorem upper_reach_9209 : UpperReach 9209 90982905434694 := by
  have hr := row_9209
  have hl := log_bounds hr.1
    (by change logScale (9209 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9203) (H := 90891626069195) (u := 91279365423)
    (by norm_num) (by norm_num) hr.1 gap_9209 hl.2
    (by norm_num) upper_reach_9203

theorem upper_reach_9221 : UpperReach 9221 91074197822441 := by
  have hr := row_9221
  have hl := log_bounds hr.1
    (by change logScale (9221 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9209) (H := 90982905434694) (u := 91292387671)
    (by norm_num) (by norm_num) hr.1 gap_9221 hl.2
    (by norm_num) upper_reach_9209

theorem upper_reach_9227 : UpperReach 9227 91165496714958 := by
  have hr := row_9227
  have hl := log_bounds hr.1
    (by change logScale (9227 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9221) (H := 91074197822441) (u := 91298892441)
    (by norm_num) (by norm_num) hr.1 gap_9227 hl.2
    (by norm_num) upper_reach_9221

theorem upper_reach_9239 : UpperReach 9239 91256808604336 := by
  have hr := row_9239
  have hl := log_bounds hr.1
    (by change logScale (9239 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9227) (H := 91165496714958) (u := 91311889302)
    (by norm_num) (by norm_num) hr.1 gap_9239 hl.2
    (by norm_num) upper_reach_9227

theorem upper_reach_9241 : UpperReach 9241 91348122658217 := by
  have hr := row_9241
  have hl := log_bounds hr.1
    (by change logScale (9241 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9239) (H := 91256808604336) (u := 91314053805)
    (by norm_num) (by norm_num) hr.1 gap_9241 hl.2
    (by norm_num) upper_reach_9239

theorem upper_reach_9257 : UpperReach 9257 91439454011269 := by
  have hr := row_9257
  have hl := log_bounds hr.1
    (by change logScale (9257 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9241) (H := 91348122658217) (u := 91331352976)
    (by norm_num) (by norm_num) hr.1 gap_9257 hl.2
    (by norm_num) upper_reach_9241

theorem upper_reach_9277 : UpperReach 9277 91530806946287 := by
  have hr := row_9277
  have hl := log_bounds hr.1
    (by change logScale (9277 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9257) (H := 91439454011269) (u := 91352934942)
    (by norm_num) (by norm_num) hr.1 gap_9277 hl.2
    (by norm_num) upper_reach_9257

theorem upper_reach_9281 : UpperReach 9281 91622164192115 := by
  have hr := row_9281
  have hl := log_bounds hr.1
    (by change logScale (9281 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9277) (H := 91530806946287) (u := 91357245752)
    (by norm_num) (by norm_num) hr.1 gap_9281 hl.2
    (by norm_num) upper_reach_9277

theorem upper_reach_9283 : UpperReach 9283 91713523592651 := by
  have hr := row_9283
  have hl := log_bounds hr.1
    (by change logScale (9283 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9281) (H := 91622164192115) (u := 91359400460)
    (by norm_num) (by norm_num) hr.1 gap_9283 hl.2
    (by norm_num) upper_reach_9281

theorem upper_reach_9293 : UpperReach 9293 91804893759768 := by
  have hr := row_9293
  have hl := log_bounds hr.1
    (by change logScale (9293 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9283) (H := 91713523592651) (u := 91370167041)
    (by norm_num) (by norm_num) hr.1 gap_9293 hl.2
    (by norm_num) upper_reach_9283

theorem upper_reach_9311 : UpperReach 9311 91896283277569 := by
  have hr := row_9311
  have hl := log_bounds hr.1
    (by change logScale (9311 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9293) (H := 91804893759768) (u := 91389517725)
    (by norm_num) (by norm_num) hr.1 gap_9311 hl.2
    (by norm_num) upper_reach_9293

theorem upper_reach_9319 : UpperReach 9319 91987681383669 := by
  have hr := row_9319
  have hl := log_bounds hr.1
    (by change logScale (9319 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9311) (H := 91896283277569) (u := 91398106024)
    (by norm_num) (by norm_num) hr.1 gap_9319 hl.2
    (by norm_num) upper_reach_9311

theorem upper_reach_9323 : UpperReach 9323 92079083781154 := by
  have hr := row_9323
  have hl := log_bounds hr.1
    (by change logScale (9323 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9319) (H := 91987681383669) (u := 91402397409)
    (by norm_num) (by norm_num) hr.1 gap_9323 hl.2
    (by norm_num) upper_reach_9319

theorem upper_reach_9337 : UpperReach 9337 92170501184001 := by
  have hr := row_9337
  have hl := log_bounds hr.1
    (by change logScale (9337 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9323) (H := 92079083781154) (u := 91417402771)
    (by norm_num) (by norm_num) hr.1 gap_9337 hl.2
    (by norm_num) upper_reach_9323

theorem upper_reach_9341 : UpperReach 9341 92261922869961 := by
  have hr := row_9341
  have hl := log_bounds hr.1
    (by change logScale (9341 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9337) (H := 92170501184001) (u := 91421685884)
    (by norm_num) (by norm_num) hr.1 gap_9341 hl.2
    (by norm_num) upper_reach_9337

theorem upper_reach_9343 : UpperReach 9343 92353346696791 := by
  have hr := row_9343
  have hl := log_bounds hr.1
    (by change logScale (9343 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9341) (H := 92261922869961) (u := 91423826754)
    (by norm_num) (by norm_num) hr.1 gap_9343 hl.2
    (by norm_num) upper_reach_9341

theorem upper_reach_9349 : UpperReach 9349 92444776943480 := by
  have hr := row_9349
  have hl := log_bounds hr.1
    (by change logScale (9349 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9343) (H := 92353346696791) (u := 91430246613)
    (by norm_num) (by norm_num) hr.1 gap_9349 hl.2
    (by norm_num) upper_reach_9343

theorem upper_reach_9371 : UpperReach 9371 92536230694453 := by
  have hr := row_9371
  have hl := log_bounds hr.1
    (by change logScale (9371 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9349) (H := 92444776943480) (u := 91453750897)
    (by norm_num) (by norm_num) hr.1 gap_9371 hl.2
    (by norm_num) upper_reach_9349

theorem upper_reach_9377 : UpperReach 9377 92627690846109 := by
  have hr := row_9377
  have hl := log_bounds hr.1
    (by change logScale (9377 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9371) (H := 92536230694453) (u := 91460151580)
    (by norm_num) (by norm_num) hr.1 gap_9377 hl.2
    (by norm_num) upper_reach_9371

theorem upper_reach_9391 : UpperReach 9391 92719165916779 := by
  have hr := row_9391
  have hl := log_bounds hr.1
    (by change logScale (9391 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9377) (H := 92627690846109) (u := 91475070594)
    (by norm_num) (by norm_num) hr.1 gap_9391 hl.2
    (by norm_num) upper_reach_9377

theorem upper_reach_9397 : UpperReach 9397 92810647374505 := by
  have hr := row_9397
  have hl := log_bounds hr.1
    (by change logScale (9397 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9391) (H := 92719165916779) (u := 91481457650)
    (by norm_num) (by norm_num) hr.1 gap_9397 hl.2
    (by norm_num) upper_reach_9391

theorem upper_reach_9403 : UpperReach 9403 92902135215209 := by
  have hr := row_9403
  have hl := log_bounds hr.1
    (by change logScale (9403 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9397) (H := 92810647374505) (u := 91487840628)
    (by norm_num) (by norm_num) hr.1 gap_9403 hl.2
    (by norm_num) upper_reach_9397

theorem upper_reach_9413 : UpperReach 9413 92993633685166 := by
  have hr := row_9413
  have hl := log_bounds hr.1
    (by change logScale (9413 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9403) (H := 92902135215209) (u := 91498469881)
    (by norm_num) (by norm_num) hr.1 gap_9413 hl.2
    (by norm_num) upper_reach_9403

#print axioms upper_reach_9413

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
