import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper015
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block016

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_4289 : UpperReach 4289 42359909963805 := by
  have hr := row_4289
  have hl := log_bounds hr.1
    (by change logScale (4289 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4283) (H := 42276271874916) (u := 83638088813)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4283

theorem upper_reach_4297 : UpperReach 4297 42443566687687 := by
  have hr := row_4297
  have hl := log_bounds hr.1
    (by change logScale (4297 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4289) (H := 42359909963805) (u := 83656723806)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4289

theorem upper_reach_4327 : UpperReach 4327 42527292985134 := by
  have hr := row_4327
  have hl := log_bounds hr.1
    (by change logScale (4327 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4297) (H := 42443566687687) (u := 83726297371)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 13, 2, 3, 2, 59, 2, 31, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4297

theorem upper_reach_4337 : UpperReach 4337 42611042366617 := by
  have hr := row_4337
  have hl := log_bounds hr.1
    (by change logScale (4337 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4327) (H := 42527292985134) (u := 83749381407)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 61, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4327

theorem upper_reach_4339 : UpperReach 4339 42694796358519 := by
  have hr := row_4339
  have hl := log_bounds hr.1
    (by change logScale (4339 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4337) (H := 42611042366617) (u := 83753991826)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4337

theorem upper_reach_4349 : UpperReach 4349 42778573370689 := by
  have hr := row_4349
  have hl := log_bounds hr.1
    (by change logScale (4349 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4339) (H := 42694796358519) (u := 83777012094)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4339

theorem upper_reach_4357 : UpperReach 4357 42862368760994 := by
  have hr := row_4357
  have hl := log_bounds hr.1
    (by change logScale (4357 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4349) (H := 42778573370689) (u := 83795390229)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4349

theorem upper_reach_4363 : UpperReach 4363 42946177912770 := by
  have hr := row_4363
  have hl := log_bounds hr.1
    (by change logScale (4363 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4357) (H := 42862368760994) (u := 83809151700)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4357

theorem upper_reach_4373 : UpperReach 4373 43030009958328 := by
  have hr := row_4373
  have hl := log_bounds hr.1
    (by change logScale (4373 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4363) (H := 42946177912770) (u := 83832045482)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4363

theorem upper_reach_4391 : UpperReach 4391 43113883081078 := by
  have hr := row_4391
  have hl := log_bounds hr.1
    (by change logScale (4391 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4373) (H := 43030009958328) (u := 83873122674)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4373

theorem upper_reach_4397 : UpperReach 4397 43197769858814 := by
  have hr := row_4397
  have hl := log_bounds hr.1
    (by change logScale (4397 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4391) (H := 43113883081078) (u := 83886777660)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4391

theorem upper_reach_4409 : UpperReach 4409 43281683890712 := by
  have hr := row_4409
  have hl := log_bounds hr.1
    (by change logScale (4409 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4397) (H := 43197769858814) (u := 83914031822)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 53, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4397

theorem upper_reach_4421 : UpperReach 4421 43365625102695 := by
  have hr := row_4421
  have hl := log_bounds hr.1
    (by change logScale (4421 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4409) (H := 43281683890712) (u := 83941211907)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4409

theorem upper_reach_4423 : UpperReach 4423 43449570837518 := by
  have hr := row_4423
  have hl := log_bounds hr.1
    (by change logScale (4423 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4421) (H := 43365625102695) (u := 83945734747)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4421

theorem upper_reach_4441 : UpperReach 4441 43533557186115 := by
  have hr := row_4441
  have hl := log_bounds hr.1
    (by change logScale (4441 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4423) (H := 43449570837518) (u := 83986348521)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 43, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4423

theorem upper_reach_4447 : UpperReach 4447 43617557036064 := by
  have hr := row_4447
  have hl := log_bounds hr.1
    (by change logScale (4447 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4441) (H := 43533557186115) (u := 83999849873)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4441

theorem upper_reach_4451 : UpperReach 4451 43701565876798 := by
  have hr := row_4451
  have hl := log_bounds hr.1
    (by change logScale (4451 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4447) (H := 43617557036064) (u := 84008840658)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4447

theorem upper_reach_4457 : UpperReach 4457 43785588188572 := by
  have hr := row_4457
  have hl := log_bounds hr.1
    (by change logScale (4457 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4451) (H := 43701565876798) (u := 84022311698)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 61, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4451

theorem upper_reach_4463 : UpperReach 4463 43869623953263 := by
  have hr := row_4463
  have hl := log_bounds hr.1
    (by change logScale (4463 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4457) (H := 43785588188572) (u := 84035764615)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4457

theorem upper_reach_4481 : UpperReach 4481 43953699968455 := by
  have hr := row_4481
  have hl := log_bounds hr.1
    (by change logScale (4481 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4463) (H := 43869623953263) (u := 84076015116)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 41, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4463

theorem upper_reach_4483 : UpperReach 4483 44037780445941 := by
  have hr := row_4483
  have hl := log_bounds hr.1
    (by change logScale (4483 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4481) (H := 43953699968455) (u := 84080477410)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4481

theorem upper_reach_4493 : UpperReach 4493 44121883205076 := by
  have hr := row_4493
  have hl := log_bounds hr.1
    (by change logScale (4493 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4483) (H := 44037780445941) (u := 84102759059)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 67, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4483

theorem upper_reach_4507 : UpperReach 4507 44206017075347 := by
  have hr := row_4507
  have hl := log_bounds hr.1
    (by change logScale (4507 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4493) (H := 44121883205076) (u := 84133870195)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4493

theorem upper_reach_4513 : UpperReach 4513 44290164249390 := by
  have hr := row_4513
  have hl := log_bounds hr.1
    (by change logScale (4513 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4507) (H := 44206017075347) (u := 84147173967)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4507

#print axioms upper_reach_4513

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
