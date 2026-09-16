import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0481
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11369 : PrimeGap 11353 11369 :=
  (primeGap_of_factors (ds := [2, 3, 2, 41, 2, 37, 2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11369 :
    (11369 : ℕ).Prime ∧ logScale (11369 : ℚ) = 13 ∧
      (93386456287 : ℤ) = ⌊logCenter (11369 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11369 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11369 : Reach 11369 112316051198395 166478426532 := by
  have hr := row_11369
  have hl := log_bounds hr.1
    (by change logScale (11369 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11353) (T := 112222664742108) (U := 166463783342)
    (by norm_num) (by norm_num) hr.1 gap_11369
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11353

theorem gap_11383 : PrimeGap 11369 11383 :=
  (primeGap_of_factors (ds := [2, 83, 2, 3, 2, 5, 2, 31, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11383 :
    (11383 : ℕ).Prime ∧ logScale (11383 : ℚ) = 13 ∧
      (93398762899 : ℤ) = ⌊logCenter (11383 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11383 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11383 : Reach 11383 112409449961294 166493052998 := by
  have hr := row_11383
  have hl := log_bounds hr.1
    (by change logScale (11383 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11369) (T := 112316051198395) (U := 166478426532)
    (by norm_num) (by norm_num) hr.1 gap_11383
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11369

theorem gap_11393 : PrimeGap 11383 11393 :=
  (primeGap_of_factors (ds := [2, 3, 2, 59, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11393 :
    (11393 : ℕ).Prime ∧ logScale (11393 : ℚ) = 13 ∧
      (93407544073 : ℤ) = ⌊logCenter (11393 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11393 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11393 : Reach 11393 112502857505367 166507667908 := by
  have hr := row_11393
  have hl := log_bounds hr.1
    (by change logScale (11393 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11383) (T := 112409449961294) (U := 166493052998)
    (by norm_num) (by norm_num) hr.1 gap_11393
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11383

theorem gap_11399 : PrimeGap 11393 11399 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11399 :
    (11399 : ℕ).Prime ∧ logScale (11399 : ℚ) = 13 ∧
      (93412809078 : ℤ) = ⌊logCenter (11399 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11399 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11399 : Reach 11399 112596270314445 166522276407 := by
  have hr := row_11399
  have hl := log_bounds hr.1
    (by change logScale (11399 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11393) (T := 112502857505367) (U := 166507667908)
    (by norm_num) (by norm_num) hr.1 gap_11399
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11393

theorem gap_11411 : PrimeGap 11399 11411 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11411 :
    (11411 : ℕ).Prime ∧ logScale (11411 : ℚ) = 13 ∧
      (93423330780 : ℤ) = ⌊logCenter (11411 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11411 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11411 : Reach 11411 112689693645225 166536870823 := by
  have hr := row_11411
  have hl := log_bounds hr.1
    (by change logScale (11411 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11399) (T := 112596270314445) (U := 166522276407)
    (by norm_num) (by norm_num) hr.1 gap_11411
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11399

theorem gap_11423 : PrimeGap 11411 11423 :=
  (primeGap_of_factors (ds := [2, 101, 2, 3, 2, 7, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11423 :
    (11423 : ℕ).Prime ∧ logScale (11423 : ℚ) = 13 ∧
      (93433841423 : ℤ) = ⌊logCenter (11423 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11423 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11423 : Reach 11423 112783127486648 166551451183 := by
  have hr := row_11423
  have hl := log_bounds hr.1
    (by change logScale (11423 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11411) (T := 112689693645225) (U := 166536870823)
    (by norm_num) (by norm_num) hr.1 gap_11423
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11411

theorem gap_11437 : PrimeGap 11423 11437 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11437 :
    (11437 : ℕ).Prime ∧ logScale (11437 : ℚ) = 13 ∧
      (93446089894 : ℤ) = ⌊logCenter (11437 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11437 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11437 : Reach 11437 112876573576542 166566014969 := by
  have hr := row_11437
  have hl := log_bounds hr.1
    (by change logScale (11437 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11423) (T := 112783127486648) (U := 166551451183)
    (by norm_num) (by norm_num) hr.1 gap_11437
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11423

theorem gap_11443 : PrimeGap 11437 11443 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11443 :
    (11443 : ℕ).Prime ∧ logScale (11443 : ℚ) = 13 ∧
      (93451334649 : ℤ) = ⌊logCenter (11443 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11443 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11443 : Reach 11443 112970024911191 166580572391 := by
  have hr := row_11443
  have hl := log_bounds hr.1
    (by change logScale (11443 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11437) (T := 112876573576542) (U := 166566014969)
    (by norm_num) (by norm_num) hr.1 gap_11443
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11437

#print axioms reach_11443

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
