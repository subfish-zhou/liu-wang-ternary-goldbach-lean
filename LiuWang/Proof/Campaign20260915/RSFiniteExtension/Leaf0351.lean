import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0350
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8423 : PrimeGap 8419 8423 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8423 :
    (8423 : ℕ).Prime ∧ logScale (8423 : ℚ) = 13 ∧
      (90387213349 : ℤ) = ⌊logCenter (8423 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8423 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8423 : Reach 8423 82897507425162 161127046291 := by
  have hr := row_8423
  have hl := log_bounds hr.1
    (by change logScale (8423 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8419) (T := 82807120211813) (U := 161107916877)
    (by norm_num) (by norm_num) hr.1 gap_8423
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8419

theorem gap_8429 : PrimeGap 8423 8429 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8429 :
    (8429 : ℕ).Prime ∧ logScale (8429 : ℚ) = 13 ∧
      (90394334166 : ℤ) = ⌊logCenter (8429 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8429 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8429 : Reach 8429 82987901759328 161146164356 := by
  have hr := row_8429
  have hl := log_bounds hr.1
    (by change logScale (8429 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8423) (T := 82897507425162) (U := 161127046291)
    (by norm_num) (by norm_num) hr.1 gap_8429
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8423

theorem gap_8431 : PrimeGap 8429 8431 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8431 :
    (8431 : ℕ).Prime ∧ logScale (8431 : ℚ) = 13 ∧
      (90396706645 : ℤ) = ⌊logCenter (8431 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8431 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8431 : Reach 8431 83078298465973 161165280153 := by
  have hr := row_8431
  have hl := log_bounds hr.1
    (by change logScale (8431 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8429) (T := 82987901759328) (U := 161146164356)
    (by norm_num) (by norm_num) hr.1 gap_8431
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8429

theorem gap_8443 : PrimeGap 8431 8443 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8443 :
    (8443 : ℕ).Prime ∧ logScale (8443 : ℚ) = 13 ∧
      (90410929712 : ℤ) = ⌊logCenter (8443 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8443 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8443 : Reach 8443 83168709395685 161184371042 := by
  have hr := row_8443
  have hl := log_bounds hr.1
    (by change logScale (8443 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8431) (T := 83078298465973) (U := 161165280153)
    (by norm_num) (by norm_num) hr.1 gap_8443
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8431

theorem gap_8447 : PrimeGap 8443 8447 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8447 :
    (8447 : ℕ).Prime ∧ logScale (8447 : ℚ) = 13 ∧
      (90415666243 : ℤ) = ⌊logCenter (8447 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8447 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8447 : Reach 8447 83259125061928 161203455150 := by
  have hr := row_8447
  have hl := log_bounds hr.1
    (by change logScale (8447 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8443) (T := 83168709395685) (U := 161184371042)
    (by norm_num) (by norm_num) hr.1 gap_8447
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8443

theorem gap_8461 : PrimeGap 8447 8461 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 79, 2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8461 :
    (8461 : ℕ).Prime ∧ logScale (8461 : ℚ) = 13 ∧
      (90432226455 : ℤ) = ⌊logCenter (8461 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8461 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8461 : Reach 8461 83349557288383 161222509932 := by
  have hr := row_8461
  have hl := log_bounds hr.1
    (by change logScale (8461 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8447) (T := 83259125061928) (U := 161203455150)
    (by norm_num) (by norm_num) hr.1 gap_8461
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8447

theorem gap_8467 : PrimeGap 8461 8467 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8467 :
    (8467 : ℕ).Prime ∧ logScale (8467 : ℚ) = 13 ∧
      (90439315302 : ℤ) = ⌊logCenter (8467 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8467 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8467 : Reach 8467 83439996603685 161241553461 := by
  have hr := row_8467
  have hl := log_bounds hr.1
    (by change logScale (8467 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8461) (T := 83349557288383) (U := 161222509932)
    (by norm_num) (by norm_num) hr.1 gap_8467
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8461

theorem gap_8501 : PrimeGap 8467 8501 :=
  (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 37, 2, 3, 2, 7, 2, 61, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8501 :
    (8501 : ℕ).Prime ∧ logScale (8501 : ℚ) = 13 ∧
      (90479390792 : ℤ) = ⌊logCenter (8501 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8501 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8501 : Reach 8501 83530475994477 161260523056 := by
  have hr := row_8501
  have hl := log_bounds hr.1
    (by change logScale (8501 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8467) (T := 83439996603685) (U := 161241553461)
    (by norm_num) (by norm_num) hr.1 gap_8501
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8467

#print axioms reach_8501

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
