import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper010
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block011

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_3329 : UpperReach 3329 32467484709766 := by
  have hr := row_3329
  have hl := log_bounds hr.1
    (by change logScale (3329 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3323) (H := 32386380437343) (u := 81104272347)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3323

theorem upper_reach_3331 : UpperReach 3331 32548594988195 := by
  have hr := row_3331
  have hl := log_bounds hr.1
    (by change logScale (3331 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3329) (H := 32467484709766) (u := 81110278353)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3329

theorem upper_reach_3343 : UpperReach 3343 32629741227106 := by
  have hr := row_3343
  have hl := log_bounds hr.1
    (by change logScale (3343 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3331) (H := 32548594988195) (u := 81146238835)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 47, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3331

theorem upper_reach_3347 : UpperReach 3347 32710899424165 := by
  have hr := row_3347
  have hl := log_bounds hr.1
    (by change logScale (3347 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3343) (H := 32629741227106) (u := 81158196983)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3343

theorem upper_reach_3359 : UpperReach 3359 32792093410108 := by
  have hr := row_3359
  have hl := log_bounds hr.1
    (by change logScale (3359 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3347) (H := 32710899424165) (u := 81193985867)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3347

theorem upper_reach_3361 : UpperReach 3361 32873293348432 := by
  have hr := row_3361
  have hl := log_bounds hr.1
    (by change logScale (3361 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3359) (H := 32792093410108) (u := 81199938248)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3359

theorem upper_reach_3371 : UpperReach 3371 32954522995631 := by
  have hr := row_3371
  have hl := log_bounds hr.1
    (by change logScale (3371 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3361) (H := 32873293348432) (u := 81229647123)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3361

theorem upper_reach_3373 : UpperReach 3373 33035758574029 := by
  have hr := row_3373
  have hl := log_bounds hr.1
    (by change logScale (3373 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3371) (H := 32954522995631) (u := 81235578322)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3371

theorem upper_reach_3389 : UpperReach 3389 33117041475792 := by
  have hr := row_3389
  have hl := log_bounds hr.1
    (by change logScale (3389 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3373) (H := 33035758574029) (u := 81282901687)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 31, 2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3373

theorem upper_reach_3391 : UpperReach 3391 33198330277260 := by
  have hr := row_3391
  have hl := log_bounds hr.1
    (by change logScale (3391 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3389) (H := 33117041475792) (u := 81288801392)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3389

theorem upper_reach_3407 : UpperReach 3407 33279666151484 := by
  have hr := row_3407
  have hl := log_bounds hr.1
    (by change logScale (3407 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3391) (H := 33198330277260) (u := 81335874148)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 43, 2, 3, 2, 19, 2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3391

theorem upper_reach_3413 : UpperReach 3413 33361019621020 := by
  have hr := row_3413
  have hl := log_bounds hr.1
    (by change logScale (3413 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3407) (H := 33279666151484) (u := 81353469460)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3407

theorem upper_reach_3433 : UpperReach 3433 33442431519001 := by
  have hr := row_3433
  have hl := log_bounds hr.1
    (by change logScale (3433 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3413) (H := 33361019621020) (u := 81411897905)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 23, 2, 3, 2, 47, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3413

theorem upper_reach_3449 : UpperReach 3449 33523889915177 := by
  have hr := row_3449
  have hl := log_bounds hr.1
    (by change logScale (3449 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3433) (H := 33442431519001) (u := 81458396100)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3433

theorem upper_reach_3457 : UpperReach 3457 33605371479623 := by
  have hr := row_3457
  have hl := log_bounds hr.1
    (by change logScale (3457 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3449) (H := 33523889915177) (u := 81481564370)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3449

theorem upper_reach_3461 : UpperReach 3461 33686864608106 := by
  have hr := row_3461
  have hl := log_bounds hr.1
    (by change logScale (3461 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3457) (H := 33605371479623) (u := 81493128407)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3457

theorem upper_reach_3463 : UpperReach 3463 33768363513597 := by
  have hr := row_3463
  have hl := log_bounds hr.1
    (by change logScale (3463 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3461) (H := 33686864608106) (u := 81498905415)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3461

theorem upper_reach_3467 : UpperReach 3467 33849873963101 := by
  have hr := row_3467
  have hl := log_bounds hr.1
    (by change logScale (3467 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3463) (H := 33768363513597) (u := 81510449428)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3463

theorem upper_reach_3469 : UpperReach 3469 33931390179618 := by
  have hr := row_3469
  have hl := log_bounds hr.1
    (by change logScale (3469 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3467) (H := 33849873963101) (u := 81516216441)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3467

theorem upper_reach_3491 : UpperReach 3491 34012969614736 := by
  have hr := row_3491
  have hl := log_bounds hr.1
    (by change logScale (3491 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3469) (H := 33931390179618) (u := 81579435042)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3469

theorem upper_reach_3499 : UpperReach 3499 34094571939707 := by
  have hr := row_3499
  have hl := log_bounds hr.1
    (by change logScale (3499 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3491) (H := 34012969614736) (u := 81602324895)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3491

theorem upper_reach_3511 : UpperReach 3511 34176208501516 := by
  have hr := row_3511
  have hl := log_bounds hr.1
    (by change logScale (3511 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3499) (H := 34094571939707) (u := 81636561733)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3499

theorem upper_reach_3517 : UpperReach 3517 34257862137888 := by
  have hr := row_3517
  have hl := log_bounds hr.1
    (by change logScale (3517 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3511) (H := 34176208501516) (u := 81653636296)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3511

theorem upper_reach_3527 : UpperReach 3527 34339544167237 := by
  have hr := row_3527
  have hl := log_bounds hr.1
    (by change logScale (3527 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3517) (H := 34257862137888) (u := 81682029273)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3517

#print axioms upper_reach_3527

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
