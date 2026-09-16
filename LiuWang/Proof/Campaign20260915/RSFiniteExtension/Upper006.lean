import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper005
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_2351 : UpperReach 2351 22933814194726 := by
  have hr := row_2351
  have hl := log_bounds hr.1
    (by change logScale (2351 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2347) (H := 22856188234194) (u := 77625960456)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2347

theorem upper_reach_2357 : UpperReach 2357 23011465643802 := by
  have hr := row_2357
  have hl := log_bounds hr.1
    (by change logScale (2357 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2351) (H := 22933814194726) (u := 77651449000)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2351

theorem upper_reach_2371 : UpperReach 2371 23089176314710 := by
  have hr := row_2371
  have hl := log_bounds hr.1
    (by change logScale (2371 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2357) (H := 23011465643802) (u := 77710670832)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2357

theorem upper_reach_2377 : UpperReach 2377 23166912259431 := by
  have hr := row_2377
  have hl := log_bounds hr.1
    (by change logScale (2377 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2371) (H := 23089176314710) (u := 77735944645)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2371

theorem upper_reach_2381 : UpperReach 2381 23244665017943 := by
  have hr := row_2381
  have hl := log_bounds hr.1
    (by change logScale (2381 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2377) (H := 23166912259431) (u := 77752758436)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2377

theorem upper_reach_2383 : UpperReach 2383 23322426172761 := by
  have hr := row_2383
  have hl := log_bounds hr.1
    (by change logScale (2383 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2381) (H := 23244665017943) (u := 77761154742)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2381

theorem upper_reach_2389 : UpperReach 2389 23400212474281 := by
  have hr := row_2389
  have hl := log_bounds hr.1
    (by change logScale (2389 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2383) (H := 23322426172761) (u := 77786301444)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2383

theorem upper_reach_2393 : UpperReach 2393 23478015505207 := by
  have hr := row_2393
  have hl := log_bounds hr.1
    (by change logScale (2393 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2389) (H := 23400212474281) (u := 77803030850)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2389

theorem upper_reach_2399 : UpperReach 2399 23555843577882 := by
  have hr := row_2399
  have hl := log_bounds hr.1
    (by change logScale (2399 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2393) (H := 23478015505207) (u := 77828072599)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2393

theorem upper_reach_2411 : UpperReach 2411 23633721546711 := by
  have hr := row_2411
  have hl := log_bounds hr.1
    (by change logScale (2411 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2399) (H := 23555843577882) (u := 77877968753)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2399

theorem upper_reach_2417 : UpperReach 2417 23711624370565 := by
  have hr := row_2417
  have hl := log_bounds hr.1
    (by change logScale (2417 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2411) (H := 23633721546711) (u := 77902823778)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2411

theorem upper_reach_2423 : UpperReach 2423 23789551987820 := by
  have hr := row_2423
  have hl := log_bounds hr.1
    (by change logScale (2423 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2417) (H := 23711624370565) (u := 77927617179)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2417

theorem upper_reach_2437 : UpperReach 2437 23867537218403 := by
  have hr := row_2437
  have hl := log_bounds hr.1
    (by change logScale (2437 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2423) (H := 23789551987820) (u := 77985230507)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2423

theorem upper_reach_2441 : UpperReach 2441 23945538849154 := by
  have hr := row_2441
  have hl := log_bounds hr.1
    (by change logScale (2441 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2437) (H := 23867537218403) (u := 78001630675)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2437

theorem upper_reach_2447 : UpperReach 2447 24023565029835 := by
  have hr := row_2447
  have hl := log_bounds hr.1
    (by change logScale (2447 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2441) (H := 23945538849154) (u := 78026180605)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2441

theorem upper_reach_2459 : UpperReach 2459 24101640130304 := by
  have hr := row_2459
  have hl := log_bounds hr.1
    (by change logScale (2459 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2447) (H := 24023565029835) (u := 78075100393)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2447

theorem upper_reach_2467 : UpperReach 2467 24179747711516 := by
  have hr := row_2467
  have hl := log_bounds hr.1
    (by change logScale (2467 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2459) (H := 24101640130304) (u := 78107581136)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2459

theorem upper_reach_2473 : UpperReach 2473 24257879584238 := by
  have hr := row_2473
  have hl := log_bounds hr.1
    (by change logScale (2473 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2467) (H := 24179747711516) (u := 78131872646)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2467

theorem upper_reach_2477 : UpperReach 2477 24336027618580 := by
  have hr := row_2477
  have hl := log_bounds hr.1
    (by change logScale (2477 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2473) (H := 24257879584238) (u := 78148034266)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2473

theorem upper_reach_2503 : UpperReach 2503 24414280071541 := by
  have hr := row_2503
  have hl := log_bounds hr.1
    (by change logScale (2503 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2477) (H := 24336027618580) (u := 78252452885)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 37, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 47, 2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2477

theorem upper_reach_2521 : UpperReach 2521 24492604180860 := by
  have hr := row_2521
  have hl := log_bounds hr.1
    (by change logScale (2521 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2503) (H := 24414280071541) (u := 78324109243)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2503

theorem upper_reach_2531 : UpperReach 2531 24570967878512 := by
  have hr := row_2531
  have hl := log_bounds hr.1
    (by change logScale (2531 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2521) (H := 24492604180860) (u := 78363697576)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2521

theorem upper_reach_2539 : UpperReach 2539 24649363134376 := by
  have hr := row_2539
  have hl := log_bounds hr.1
    (by change logScale (2539 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2531) (H := 24570967878512) (u := 78395255788)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2531

theorem upper_reach_2543 : UpperReach 2543 24727774132077 := by
  have hr := row_2543
  have hl := log_bounds hr.1
    (by change logScale (2543 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2539) (H := 24649363134376) (u := 78410997625)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2539

#print axioms upper_reach_2543

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
