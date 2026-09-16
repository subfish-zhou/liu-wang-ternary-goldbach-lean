import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0541
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12703 : PrimeGap 12697 12703 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12703 :
    (12703 : ℕ).Prime ∧ logScale (12703 : ℚ) = 13 ∧
      (94495934616 : ℤ) = ⌊logCenter (12703 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12703 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12703 : Reach 12703 125848727243174 168479164799 := by
  have hr := row_12703
  have hl := log_bounds hr.1
    (by change logScale (12703 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12697) (T := 125754231308558) (U := 168465901856)
    (by norm_num) (by norm_num) hr.1 gap_12703
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12697

theorem gap_12713 : PrimeGap 12703 12713 :=
  (primeGap_of_factors (ds := [2, 3, 2, 97, 2, 71, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12713 :
    (12713 : ℕ).Prime ∧ logScale (12713 : ℚ) = 13 ∧
      (94503803675 : ℤ) = ⌊logCenter (12713 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12713 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12713 : Reach 12713 125943231046849 168492418352 := by
  have hr := row_12713
  have hl := log_bounds hr.1
    (by change logScale (12713 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12703) (T := 125848727243174) (U := 168479164799)
    (by norm_num) (by norm_num) hr.1 gap_12713
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12703

theorem gap_12721 : PrimeGap 12713 12721 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12721 :
    (12721 : ℕ).Prime ∧ logScale (12721 : ℚ) = 13 ∧
      (94510094467 : ℤ) = ⌊logCenter (12721 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12721 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12721 : Reach 12721 126037741141316 168505664612 := by
  have hr := row_12721
  have hl := log_bounds hr.1
    (by change logScale (12721 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12713) (T := 125943231046849) (U := 168492418352)
    (by norm_num) (by norm_num) hr.1 gap_12721
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12713

theorem gap_12739 : PrimeGap 12721 12739 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 29, 2, 7, 2, 3, 2, 47, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12739 :
    (12739 : ℕ).Prime ∧ logScale (12739 : ℚ) = 13 ∧
      (94524234297 : ℤ) = ⌊logCenter (12739 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12739 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12739 : Reach 12739 126132265375613 168518893193 := by
  have hr := row_12739
  have hl := log_bounds hr.1
    (by change logScale (12739 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12721) (T := 126037741141316) (U := 168505664612)
    (by norm_num) (by norm_num) hr.1 gap_12739
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12721

theorem gap_12743 : PrimeGap 12739 12743 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12743 :
    (12743 : ℕ).Prime ∧ logScale (12743 : ℚ) = 13 ∧
      (94527373768 : ℤ) = ⌊logCenter (12743 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12743 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12743 : Reach 12743 126226792749381 168532118660 := by
  have hr := row_12743
  have hl := log_bounds hr.1
    (by change logScale (12743 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12739) (T := 126132265375613) (U := 168518893193)
    (by norm_num) (by norm_num) hr.1 gap_12743
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12739

theorem gap_12757 : PrimeGap 12743 12757 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 41, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12757 :
    (12757 : ℕ).Prime ∧ logScale (12757 : ℚ) = 13 ∧
      (94538354161 : ℤ) = ⌊logCenter (12757 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12757 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12757 : Reach 12757 126321331103542 168545330648 := by
  have hr := row_12757
  have hl := log_bounds hr.1
    (by change logScale (12757 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12743) (T := 126226792749381) (U := 168532118660)
    (by norm_num) (by norm_num) hr.1 gap_12757
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12743

theorem gap_12763 : PrimeGap 12757 12763 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12763 :
    (12763 : ℕ).Prime ∧ logScale (12763 : ℚ) = 13 ∧
      (94543056356 : ℤ) = ⌊logCenter (12763 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12763 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12763 : Reach 12763 126415874159898 168558537460 := by
  have hr := row_12763
  have hl := log_bounds hr.1
    (by change logScale (12763 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12757) (T := 126321331103542) (U := 168545330648)
    (by norm_num) (by norm_num) hr.1 gap_12763
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12757

theorem gap_12781 : PrimeGap 12763 12781 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 113, 2, 3, 2, 53, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12781 :
    (12781 : ℕ).Prime ∧ logScale (12781 : ℚ) = 13 ∧
      (94557149687 : ℤ) = ⌊logCenter (12781 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12781 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12781 : Reach 12781 126510431309585 168571726704 := by
  have hr := row_12781
  have hl := log_bounds hr.1
    (by change logScale (12781 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12763) (T := 126415874159898) (U := 168558537460)
    (by norm_num) (by norm_num) hr.1 gap_12781
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12763

#print axioms reach_12781

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
