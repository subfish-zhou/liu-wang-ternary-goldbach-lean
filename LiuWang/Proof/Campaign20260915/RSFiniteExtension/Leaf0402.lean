import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0401
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9539 : PrimeGap 9533 9539 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9539 :
    (9539 : ℕ).Prime ∧ logScale (9539 : ℚ) = 13 ∧
      (91631439337 : ℤ) = ⌊logCenter (9539 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9539 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9539 : Reach 9539 94550158880915 163439774334 := by
  have hr := row_9539
  have hl := log_bounds hr.1
    (by change logScale (9539 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9533) (T := 94458527441578) (U := 163422640486)
    (by norm_num) (by norm_num) hr.1 gap_9539
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9533

theorem gap_9547 : PrimeGap 9539 9547 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9547 :
    (9547 : ℕ).Prime ∧ logScale (9547 : ℚ) = 13 ∧
      (91639822446 : ℤ) = ⌊logCenter (9547 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9547 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9547 : Reach 9547 94641798703361 163456895618 := by
  have hr := row_9547
  have hl := log_bounds hr.1
    (by change logScale (9547 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9539) (T := 94550158880915) (U := 163439774334)
    (by norm_num) (by norm_num) hr.1 gap_9547
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9539

theorem gap_9551 : PrimeGap 9547 9551 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9551 :
    (9551 : ℕ).Prime ∧ logScale (9551 : ℚ) = 13 ∧
      (91644011366 : ℤ) = ⌊logCenter (9551 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9551 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9551 : Reach 9551 94733442714727 163474011524 := by
  have hr := row_9551
  have hl := log_bounds hr.1
    (by change logScale (9551 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9547) (T := 94641798703361) (U := 163456895618)
    (by norm_num) (by norm_num) hr.1 gap_9551
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9547

theorem gap_9587 : PrimeGap 9551 9587 :=
  (primeGap_of_factors (ds := [2, 41, 2, 3, 2, 19, 2, 11, 2, 3, 2, 73, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 61, 2, 3, 2, 11, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9587 :
    (9587 : ℕ).Prime ∧ logScale (9587 : ℚ) = 13 ∧
      (91681632896 : ℤ) = ⌊logCenter (9587 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9587 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9587 : Reach 9587 94825124347623 163491064937 := by
  have hr := row_9587
  have hl := log_bounds hr.1
    (by change logScale (9587 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9551) (T := 94733442714727) (U := 163474011524)
    (by norm_num) (by norm_num) hr.1 gap_9587
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9551

theorem gap_9601 : PrimeGap 9587 9601 :=
  (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 53, 2, 5, 2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9601 :
    (9601 : ℕ).Prime ∧ logScale (9601 : ℚ) = 13 ∧
      (91696225353 : ℤ) = ⌊logCenter (9601 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9601 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9601 : Reach 9601 94916820572976 163508095257 := by
  have hr := row_9601
  have hl := log_bounds hr.1
    (by change logScale (9601 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9587) (T := 94825124347623) (U := 163491064937)
    (by norm_num) (by norm_num) hr.1 gap_9601
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9587

theorem gap_9613 : PrimeGap 9601 9613 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9613 :
    (9613 : ℕ).Prime ∧ logScale (9613 : ℚ) = 13 ∧
      (91708716246 : ℤ) = ⌊logCenter (9613 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9613 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9613 : Reach 9613 95008529289222 163525106087 := by
  have hr := row_9613
  have hl := log_bounds hr.1
    (by change logScale (9613 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9601) (T := 94916820572976) (U := 163508095257)
    (by norm_num) (by norm_num) hr.1 gap_9613
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9601

theorem gap_9619 : PrimeGap 9613 9619 :=
  (primeGap_of_factors (ds := [2, 3, 2, 59, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9619 :
    (9619 : ℕ).Prime ∧ logScale (9619 : ℚ) = 13 ∧
      (91714955847 : ℤ) = ⌊logCenter (9619 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9619 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9619 : Reach 9619 95100244245069 163542108074 := by
  have hr := row_9619
  have hl := log_bounds hr.1
    (by change logScale (9619 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9613) (T := 95008529289222) (U := 163525106087)
    (by norm_num) (by norm_num) hr.1 gap_9619
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9613

theorem gap_9623 : PrimeGap 9619 9623 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9623 :
    (9623 : ℕ).Prime ∧ logScale (9623 : ℚ) = 13 ∧
      (91719113419 : ℤ) = ⌊logCenter (9623 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9623 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9623 : Reach 9623 95191963358488 163559104760 := by
  have hr := row_9623
  have hl := log_bounds hr.1
    (by change logScale (9623 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9619) (T := 95100244245069) (U := 163542108074)
    (by norm_num) (by norm_num) hr.1 gap_9623
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9619

#print axioms reach_9623

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
