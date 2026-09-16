import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0580
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13567 : PrimeGap 13553 13567 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13567 :
    (13567 : ℕ).Prime ∧ logScale (13567 : ℚ) = 13 ∧
      (95153956491 : ℤ) = ⌊logCenter (13567 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13567 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13567 : Reach 13567 134193349438695 169612523361 := by
  have hr := row_13567
  have hl := log_bounds hr.1
    (by change logScale (13567 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13553) (T := 134098195482204) (U := 169600021516)
    (by norm_num) (by norm_num) hr.1 gap_13567
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13553

theorem gap_13577 : PrimeGap 13567 13577 :=
  (primeGap_of_factors (ds := [2, 3, 2, 41, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13577 :
    (13577 : ℕ).Prime ∧ logScale (13577 : ℚ) = 13 ∧
      (95161324602 : ℤ) = ⌊logCenter (13577 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13577 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13577 : Reach 13577 134288510763297 169625016918 := by
  have hr := row_13577
  have hl := log_bounds hr.1
    (by change logScale (13577 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13567) (T := 134193349438695) (U := 169612523361)
    (by norm_num) (by norm_num) hr.1 gap_13577
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13567

theorem gap_13591 : PrimeGap 13577 13591 :=
  (primeGap_of_factors (ds := [2, 37, 2, 3, 2, 17, 2, 5, 2, 3, 2, 107, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13591 :
    (13591 : ℕ).Prime ∧ logScale (13591 : ℚ) = 13 ∧
      (95171630845 : ℤ) = ⌊logCenter (13591 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13591 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13591 : Reach 13591 134383682394142 169637498524 := by
  have hr := row_13591
  have hl := log_bounds hr.1
    (by change logScale (13591 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13577) (T := 134288510763297) (U := 169625016918)
    (by norm_num) (by norm_num) hr.1 gap_13591
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13577

theorem gap_13597 : PrimeGap 13591 13597 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13597 :
    (13597 : ℕ).Prime ∧ logScale (13597 : ℚ) = 13 ∧
      (95176044557 : ℤ) = ⌊logCenter (13597 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13597 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13597 : Reach 13597 134478858438699 169649975540 := by
  have hr := row_13597
  have hl := log_bounds hr.1
    (by change logScale (13597 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13591) (T := 134383682394142) (U := 169637498524)
    (by norm_num) (by norm_num) hr.1 gap_13597
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13591

theorem gap_13613 : PrimeGap 13597 13613 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 61, 2, 3, 2, 11, 2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13613 :
    (13613 : ℕ).Prime ∧ logScale (13613 : ℚ) = 13 ∧
      (95187804941 : ℤ) = ⌊logCenter (13613 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13613 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13613 : Reach 13613 134574046243640 169662438806 := by
  have hr := row_13613
  have hl := log_bounds hr.1
    (by change logScale (13613 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13597) (T := 134478858438699) (U := 169649975540)
    (by norm_num) (by norm_num) hr.1 gap_13613
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13597

theorem gap_13619 : PrimeGap 13613 13619 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13619 :
    (13619 : ℕ).Prime ∧ logScale (13619 : ℚ) = 13 ∧
      (95192211521 : ℤ) = ⌊logCenter (13619 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13619 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13619 : Reach 13619 134669238455161 169674897496 := by
  have hr := row_13619
  have hl := log_bounds hr.1
    (by change logScale (13619 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13613) (T := 134574046243640) (U := 169662438806)
    (by norm_num) (by norm_num) hr.1 gap_13619
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13613

theorem gap_13627 : PrimeGap 13619 13627 :=
  (primeGap_of_factors (ds := [2, 53, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13627 :
    (13627 : ℕ).Prime ∧ logScale (13627 : ℚ) = 13 ∧
      (95198083943 : ℤ) = ⌊logCenter (13627 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13627 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13627 : Reach 13627 134764436539104 169687349786 := by
  have hr := row_13627
  have hl := log_bounds hr.1
    (by change logScale (13627 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13619) (T := 134669238455161) (U := 169674897496)
    (by norm_num) (by norm_num) hr.1 gap_13627
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13619

theorem gap_13633 : PrimeGap 13627 13633 :=
  (primeGap_of_factors (ds := [2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13633 :
    (13633 : ℕ).Prime ∧ logScale (13633 : ℚ) = 13 ∧
      (95202485998 : ℤ) = ⌊logCenter (13633 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13633 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13633 : Reach 13633 134859639025102 169699797509 := by
  have hr := row_13633
  have hl := log_bounds hr.1
    (by change logScale (13633 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13627) (T := 134764436539104) (U := 169687349786)
    (by norm_num) (by norm_num) hr.1 gap_13633
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13627

#print axioms reach_13633

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
