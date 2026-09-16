import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0441
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10433 : PrimeGap 10429 10433 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10433 :
    (10433 : ℕ).Prime ∧ logScale (10433 : ℚ) = 13 ∧
      (92527291350 : ℤ) = ⌊logCenter (10433 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10433 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10433 : Reach 10433 103391126892921 165018523924 := by
  have hr := row_10433
  have hl := log_bounds hr.1
    (by change logScale (10433 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10429) (T := 103298599601571) (U := 165002706946)
    (by norm_num) (by norm_num) hr.1 gap_10433
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10429

theorem gap_10453 : PrimeGap 10433 10453 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10453 :
    (10453 : ℕ).Prime ∧ logScale (10453 : ℚ) = 13 ∧
      (92546442941 : ℤ) = ⌊logCenter (10453 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10453 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10453 : Reach 10453 103483673335862 165034312149 := by
  have hr := row_10453
  have hl := log_bounds hr.1
    (by change logScale (10453 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10433) (T := 103391126892921) (U := 165018523924)
    (by norm_num) (by norm_num) hr.1 gap_10453
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10433

theorem gap_10457 : PrimeGap 10453 10457 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10457 :
    (10457 : ℕ).Prime ∧ logScale (10457 : ℚ) = 13 ∧
      (92550268862 : ℤ) = ⌊logCenter (10457 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10457 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10457 : Reach 10457 103576223604724 165050095844 := by
  have hr := row_10457
  have hl := log_bounds hr.1
    (by change logScale (10457 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10453) (T := 103483673335862) (U := 165034312149)
    (by norm_num) (by norm_num) hr.1 gap_10457
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10453

theorem gap_10459 : PrimeGap 10457 10459 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10459 :
    (10459 : ℕ).Prime ∧ logScale (10459 : ℚ) = 13 ∧
      (92552181273 : ℤ) = ⌊logCenter (10459 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10459 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10459 : Reach 10459 103668775785997 165065878030 := by
  have hr := row_10459
  have hl := log_bounds hr.1
    (by change logScale (10459 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10457) (T := 103576223604724) (U := 165050095844)
    (by norm_num) (by norm_num) hr.1 gap_10459
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10457

theorem gap_10463 : PrimeGap 10459 10463 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10463 :
    (10463 : ℕ).Prime ∧ logScale (10463 : ℚ) = 13 ∧
      (92556005000 : ℤ) = ⌊logCenter (10463 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10463 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10463 : Reach 10463 103761331790997 165081655690 := by
  have hr := row_10463
  have hl := log_bounds hr.1
    (by change logScale (10463 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10459) (T := 103668775785997) (U := 165065878030)
    (by norm_num) (by norm_num) hr.1 gap_10463
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10459

theorem gap_10477 : PrimeGap 10463 10477 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 19, 2, 37, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10477 :
    (10477 : ℕ).Prime ∧ logScale (10477 : ℚ) = 13 ∧
      (92569376539 : ℤ) = ⌊logCenter (10477 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10477 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10477 : Reach 10477 103853901167536 165097413771 := by
  have hr := row_10477
  have hl := log_bounds hr.1
    (by change logScale (10477 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10463) (T := 103761331790997) (U := 165081655690)
    (by norm_num) (by norm_num) hr.1 gap_10477
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10463

theorem gap_10487 : PrimeGap 10477 10487 :=
  (primeGap_of_factors (ds := [2, 3, 2, 47, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10487 :
    (10487 : ℕ).Prime ∧ logScale (10487 : ℚ) = 13 ∧
      (92578916704 : ℤ) = ⌊logCenter (10487 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10487 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10487 : Reach 10487 103946480084240 165113158327 := by
  have hr := row_10487
  have hl := log_bounds hr.1
    (by change logScale (10487 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10477) (T := 103853901167536) (U := 165097413771)
    (by norm_num) (by norm_num) hr.1 gap_10487
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10477

theorem gap_10499 : PrimeGap 10487 10499 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10499 :
    (10499 : ℕ).Prime ∧ logScale (10499 : ℚ) = 13 ∧
      (92590352901 : ℤ) = ⌊logCenter (10499 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10499 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10499 : Reach 10499 104039070437141 165128886386 := by
  have hr := row_10499
  have hl := log_bounds hr.1
    (by change logScale (10499 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10487) (T := 103946480084240) (U := 165113158327)
    (by norm_num) (by norm_num) hr.1 gap_10499
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10487

#print axioms reach_10499

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
