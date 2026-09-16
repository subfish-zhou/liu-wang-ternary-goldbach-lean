import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block031
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7673 : PrimeGap 7669 7673 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7673 :
    (7673 : ℕ).Prime ∧ logScale (7673 : ℚ) = 12 ∧
      (89454629490 : ℤ) = ⌊logCenter (7673 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7673 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7673 : Reach 7673 75703283253754 159532004712 := by
  have hr := row_7673
  have hl := log_bounds hr.1
    (by change logScale (7673 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7669) (T := 75613828624264) (U := 159511213365)
    (by norm_num) (by norm_num) hr.1 gap_7673
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7669

theorem gap_7681 : PrimeGap 7673 7681 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7681 :
    (7681 : ℕ).Prime ∧ logScale (7681 : ℚ) = 12 ∧
      (89465050228 : ℤ) = ⌊logCenter (7681 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7681 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7681 : Reach 7681 75792748303982 159552777109 := by
  have hr := row_7681
  have hl := log_bounds hr.1
    (by change logScale (7681 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7673) (T := 75703283253754) (U := 159532004712)
    (by norm_num) (by norm_num) hr.1 gap_7681
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7673

theorem gap_7687 : PrimeGap 7681 7687 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7687 :
    (7687 : ℕ).Prime ∧ logScale (7687 : ℚ) = 12 ∧
      (89472858662 : ℤ) = ⌊logCenter (7687 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7687 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7687 : Reach 7687 75882221162644 159573535993 := by
  have hr := row_7687
  have hl := log_bounds hr.1
    (by change logScale (7687 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7681) (T := 75792748303982) (U := 159552777109)
    (by norm_num) (by norm_num) hr.1 gap_7687
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7681

theorem gap_7691 : PrimeGap 7687 7691 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7691 :
    (7691 : ℕ).Prime ∧ logScale (7691 : ℚ) = 12 ∧
      (89478060899 : ℤ) = ⌊logCenter (7691 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7691 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7691 : Reach 7691 75971699223543 159594286778 := by
  have hr := row_7691
  have hl := log_bounds hr.1
    (by change logScale (7691 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7687) (T := 75882221162644) (U := 159573535993)
    (by norm_num) (by norm_num) hr.1 gap_7691
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7687

theorem gap_7699 : PrimeGap 7691 7699 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7699 :
    (7699 : ℕ).Prime ∧ logScale (7699 : ℚ) = 12 ∧
      (89488457261 : ℤ) = ⌊logCenter (7699 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7699 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7699 : Reach 7699 76061187680804 159615018694 := by
  have hr := row_7699
  have hl := log_bounds hr.1
    (by change logScale (7699 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7691) (T := 75971699223543) (U := 159594286778)
    (by norm_num) (by norm_num) hr.1 gap_7699
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7691

theorem gap_7703 : PrimeGap 7699 7703 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7703 :
    (7703 : ℕ).Prime ∧ logScale (7703 : ℚ) = 12 ∧
      (89493651392 : ℤ) = ⌊logCenter (7703 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7703 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7703 : Reach 7703 76150681332196 159635742535 := by
  have hr := row_7703
  have hl := log_bounds hr.1
    (by change logScale (7703 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7699) (T := 76061187680804) (U := 159615018694)
    (by norm_num) (by norm_num) hr.1 gap_7703
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7699

theorem gap_7717 : PrimeGap 7703 7717 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7717 :
    (7717 : ℕ).Prime ∧ logScale (7717 : ℚ) = 12 ∧
      (89511809633 : ℤ) = ⌊logCenter (7717 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7717 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7717 : Reach 7717 76240193141829 159656431460 := by
  have hr := row_7717
  have hl := log_bounds hr.1
    (by change logScale (7717 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7703) (T := 76150681332196) (U := 159635742535)
    (by norm_num) (by norm_num) hr.1 gap_7717
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7703

theorem gap_7723 : PrimeGap 7717 7723 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7723 :
    (7723 : ℕ).Prime ∧ logScale (7723 : ℚ) = 12 ∧
      (89519581654 : ℤ) = ⌊logCenter (7723 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7723 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7723 : Reach 7723 76329712723483 159677106989 := by
  have hr := row_7723
  have hl := log_bounds hr.1
    (by change logScale (7723 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7717) (T := 76240193141829) (U := 159656431460)
    (by norm_num) (by norm_num) hr.1 gap_7723
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7717

#print axioms reach_7723

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
