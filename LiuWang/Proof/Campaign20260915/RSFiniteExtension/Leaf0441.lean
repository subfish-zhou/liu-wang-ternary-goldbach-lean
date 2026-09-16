import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0440
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10337 : PrimeGap 10333 10337 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10337 :
    (10337 : ℕ).Prime ∧ logScale (10337 : ℚ) = 13 ∧
      (92434849671 : ℤ) = ⌊logCenter (10337 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10337 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10337 : Reach 10337 102651212413832 164891548729 := by
  have hr := row_10337
  have hl := log_bounds hr.1
    (by change logScale (10337 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10333) (T := 102558777564161) (U := 164875597142)
    (by norm_num) (by norm_num) hr.1 gap_10337
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10333

theorem gap_10343 : PrimeGap 10337 10343 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10343 :
    (10343 : ℕ).Prime ∧ logScale (10343 : ℚ) = 13 ∧
      (92440652379 : ℤ) = ⌊logCenter (10343 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10343 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10343 : Reach 10343 102743653066211 164907492604 := by
  have hr := row_10343
  have hl := log_bounds hr.1
    (by change logScale (10343 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10337) (T := 102651212413832) (U := 164891548729)
    (by norm_num) (by norm_num) hr.1 gap_10343
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10337

theorem gap_10357 : PrimeGap 10343 10357 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 79, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10357 :
    (10357 : ℕ).Prime ∧ logScale (10357 : ℚ) = 13 ∧
      (92454178952 : ℤ) = ⌊logCenter (10357 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10357 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10357 : Reach 10357 102836107245163 164923416464 := by
  have hr := row_10357
  have hl := log_bounds hr.1
    (by change logScale (10357 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10343) (T := 102743653066211) (U := 164907492604)
    (by norm_num) (by norm_num) hr.1 gap_10357
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10343

theorem gap_10369 : PrimeGap 10357 10369 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 43, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10369 :
    (10369 : ℕ).Prime ∧ logScale (10369 : ℚ) = 13 ∧
      (92465758611 : ℤ) = ⌊logCenter (10369 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10369 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10369 : Reach 10369 102928573003774 164939323430 := by
  have hr := row_10369
  have hl := log_bounds hr.1
    (by change logScale (10369 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10357) (T := 102836107245163) (U := 164923416464)
    (by norm_num) (by norm_num) hr.1 gap_10369
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10357

theorem gap_10391 : PrimeGap 10369 10391 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 97, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10391 :
    (10391 : ℕ).Prime ∧ logScale (10391 : ℚ) = 13 ∧
      (92486953224 : ℤ) = ⌊logCenter (10391 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10391 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10391 : Reach 10391 103021059956998 164955198245 := by
  have hr := row_10391
  have hl := log_bounds hr.1
    (by change logScale (10391 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10369) (T := 102928573003774) (U := 164939323430)
    (by norm_num) (by norm_num) hr.1 gap_10391
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10369

theorem gap_10399 : PrimeGap 10391 10399 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10399 :
    (10399 : ℕ).Prime ∧ logScale (10399 : ℚ) = 13 ∧
      (92494649232 : ℤ) = ⌊logCenter (10399 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10399 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10399 : Reach 10399 103113554606230 164971062373 := by
  have hr := row_10399
  have hl := log_bounds hr.1
    (by change logScale (10399 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10391) (T := 103021059956998) (U := 164955198245)
    (by norm_num) (by norm_num) hr.1 gap_10399
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10391

theorem gap_10427 : PrimeGap 10399 10427 :=
  (primeGap_of_factors (ds := [2, 3, 2, 101, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10427 :
    (10427 : ℕ).Prime ∧ logScale (10427 : ℚ) = 13 ∧
      (92521538714 : ℤ) = ⌊logCenter (10427 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10427 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10427 : Reach 10427 103206076144944 164986885418 := by
  have hr := row_10427
  have hl := log_bounds hr.1
    (by change logScale (10427 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10399) (T := 103113554606230) (U := 164971062373)
    (by norm_num) (by norm_num) hr.1 gap_10427
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10399

theorem gap_10429 : PrimeGap 10427 10429 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10429 :
    (10429 : ℕ).Prime ∧ logScale (10429 : ℚ) = 13 ∧
      (92523456627 : ℤ) = ⌊logCenter (10429 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10429 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10429 : Reach 10429 103298599601571 165002706946 := by
  have hr := row_10429
  have hl := log_bounds hr.1
    (by change logScale (10429 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10427) (T := 103206076144944) (U := 164986885418)
    (by norm_num) (by norm_num) hr.1 gap_10429
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10427

#print axioms reach_10429

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
