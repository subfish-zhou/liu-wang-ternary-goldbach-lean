import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper047
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block048

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_11213 : UpperReach 11213 110822896204429 := by
  have hr := row_11213
  have hl := log_bounds hr.1
    (by change logScale (11213 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11197) (H := 110729647913403) (u := 93248290950)
    (by norm_num) (by norm_num) hr.1 gap_11213 hl.2
    (by norm_num) upper_reach_11197

theorem upper_reach_11239 : UpperReach 11239 110916167655986 := by
  have hr := row_11239
  have hl := log_bounds hr.1
    (by change logScale (11239 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11213) (H := 110822896204429) (u := 93271451481)
    (by norm_num) (by norm_num) hr.1 gap_11239 hl.2
    (by norm_num) upper_reach_11213

theorem upper_reach_11243 : UpperReach 11243 111009442665945 := by
  have hr := row_11243
  have hl := log_bounds hr.1
    (by change logScale (11243 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11239) (H := 110916167655986) (u := 93275009883)
    (by norm_num) (by norm_num) hr.1 gap_11243 hl.2
    (by norm_num) upper_reach_11239

theorem upper_reach_11251 : UpperReach 11251 111102724788912 := by
  have hr := row_11251
  have hl := log_bounds hr.1
    (by change logScale (11251 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11243) (H := 111009442665945) (u := 93282122891)
    (by norm_num) (by norm_num) hr.1 gap_11251 hl.2
    (by norm_num) upper_reach_11243

theorem upper_reach_11257 : UpperReach 11257 111196012243317 := by
  have hr := row_11257
  have hl := log_bounds hr.1
    (by change logScale (11257 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11251) (H := 111102724788912) (u := 93287454329)
    (by norm_num) (by norm_num) hr.1 gap_11257 hl.2
    (by norm_num) upper_reach_11251

theorem upper_reach_11261 : UpperReach 11261 111289303250436 := by
  have hr := row_11261
  have hl := log_bounds hr.1
    (by change logScale (11261 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11257) (H := 111196012243317) (u := 93291007043)
    (by norm_num) (by norm_num) hr.1 gap_11261 hl.2
    (by norm_num) upper_reach_11257

theorem upper_reach_11273 : UpperReach 11273 111382604908128 := by
  have hr := row_11273
  have hl := log_bounds hr.1
    (by change logScale (11273 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11261) (H := 111289303250436) (u := 93301657616)
    (by norm_num) (by norm_num) hr.1 gap_11273 hl.2
    (by norm_num) upper_reach_11261

theorem upper_reach_11279 : UpperReach 11279 111475911886856 := by
  have hr := row_11279
  have hl := log_bounds hr.1
    (by change logScale (11279 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11273) (H := 111382604908128) (u := 93306978652)
    (by norm_num) (by norm_num) hr.1 gap_11279 hl.2
    (by norm_num) upper_reach_11273

theorem upper_reach_11287 : UpperReach 11287 111569225955897 := by
  have hr := row_11287
  have hl := log_bounds hr.1
    (by change logScale (11287 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11279) (H := 111475911886856) (u := 93314068965)
    (by norm_num) (by norm_num) hr.1 gap_11287 hl.2
    (by norm_num) upper_reach_11279

theorem upper_reach_11299 : UpperReach 11299 111662550650991 := by
  have hr := row_11299
  have hl := log_bounds hr.1
    (by change logScale (11299 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11287) (H := 111569225955897) (u := 93324695018)
    (by norm_num) (by norm_num) hr.1 gap_11299 hl.2
    (by norm_num) upper_reach_11287

theorem upper_reach_11311 : UpperReach 11311 111755885960858 := by
  have hr := row_11311
  have hl := log_bounds hr.1
    (by change logScale (11311 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11299) (H := 111662550650991) (u := 93335309791)
    (by norm_num) (by norm_num) hr.1 gap_11311 hl.2
    (by norm_num) upper_reach_11299

theorem upper_reach_11317 : UpperReach 11317 111849226573889 := by
  have hr := row_11317
  have hl := log_bounds hr.1
    (by change logScale (11317 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11311) (H := 111755885960858) (u := 93340612955)
    (by norm_num) (by norm_num) hr.1 gap_11317 hl.2
    (by norm_num) upper_reach_11311

theorem upper_reach_11321 : UpperReach 11321 111942570720801 := by
  have hr := row_11321
  have hl := log_bounds hr.1
    (by change logScale (11321 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11317) (H := 111849226573889) (u := 93344146836)
    (by norm_num) (by norm_num) hr.1 gap_11321 hl.2
    (by norm_num) upper_reach_11317

theorem upper_reach_11329 : UpperReach 11329 112035921931731 := by
  have hr := row_11329
  have hl := log_bounds hr.1
    (by change logScale (11329 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11321) (H := 111942570720801) (u := 93351210854)
    (by norm_num) (by norm_num) hr.1 gap_11329 hl.2
    (by norm_num) upper_reach_11321

theorem upper_reach_11351 : UpperReach 11351 112129292543020 := by
  have hr := row_11351
  have hl := log_bounds hr.1
    (by change logScale (11351 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11329) (H := 112035921931731) (u := 93370611213)
    (by norm_num) (by norm_num) hr.1 gap_11351 hl.2
    (by norm_num) upper_reach_11329

theorem upper_reach_11353 : UpperReach 11353 112222664916113 := by
  have hr := row_11353
  have hl := log_bounds hr.1
    (by change logScale (11353 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11351) (H := 112129292543020) (u := 93372373017)
    (by norm_num) (by norm_num) hr.1 gap_11353 hl.2
    (by norm_num) upper_reach_11351

theorem upper_reach_11369 : UpperReach 11369 112316051372476 := by
  have hr := row_11369
  have hl := log_bounds hr.1
    (by change logScale (11369 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11353) (H := 112222664916113) (u := 93386456287)
    (by norm_num) (by norm_num) hr.1 gap_11369 hl.2
    (by norm_num) upper_reach_11353

theorem upper_reach_11383 : UpperReach 11383 112409450135451 := by
  have hr := row_11383
  have hl := log_bounds hr.1
    (by change logScale (11383 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11369) (H := 112316051372476) (u := 93398762899)
    (by norm_num) (by norm_num) hr.1 gap_11383 hl.2
    (by norm_num) upper_reach_11369

theorem upper_reach_11393 : UpperReach 11393 112502857679600 := by
  have hr := row_11393
  have hl := log_bounds hr.1
    (by change logScale (11393 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11383) (H := 112409450135451) (u := 93407544073)
    (by norm_num) (by norm_num) hr.1 gap_11393 hl.2
    (by norm_num) upper_reach_11383

theorem upper_reach_11399 : UpperReach 11399 112596270488754 := by
  have hr := row_11399
  have hl := log_bounds hr.1
    (by change logScale (11399 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11393) (H := 112502857679600) (u := 93412809078)
    (by norm_num) (by norm_num) hr.1 gap_11399 hl.2
    (by norm_num) upper_reach_11393

theorem upper_reach_11411 : UpperReach 11411 112689693819610 := by
  have hr := row_11411
  have hl := log_bounds hr.1
    (by change logScale (11411 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11399) (H := 112596270488754) (u := 93423330780)
    (by norm_num) (by norm_num) hr.1 gap_11411 hl.2
    (by norm_num) upper_reach_11399

theorem upper_reach_11423 : UpperReach 11423 112783127661109 := by
  have hr := row_11423
  have hl := log_bounds hr.1
    (by change logScale (11423 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11411) (H := 112689693819610) (u := 93433841423)
    (by norm_num) (by norm_num) hr.1 gap_11423 hl.2
    (by norm_num) upper_reach_11411

theorem upper_reach_11437 : UpperReach 11437 112876573751079 := by
  have hr := row_11437
  have hl := log_bounds hr.1
    (by change logScale (11437 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11423) (H := 112783127661109) (u := 93446089894)
    (by norm_num) (by norm_num) hr.1 gap_11437 hl.2
    (by norm_num) upper_reach_11423

theorem upper_reach_11443 : UpperReach 11443 112970025085804 := by
  have hr := row_11443
  have hl := log_bounds hr.1
    (by change logScale (11443 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11437) (H := 112876573751079) (u := 93451334649)
    (by norm_num) (by norm_num) hr.1 gap_11443 hl.2
    (by norm_num) upper_reach_11437

#print axioms upper_reach_11443

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
