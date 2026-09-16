import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0540
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12637 : PrimeGap 12619 12637 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2, 73, 2, 17, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12637 :
    (12637 : ℕ).Prime ∧ logScale (12637 : ℚ) = 13 ∧
      (94443842943 : ℤ) = ⌊logCenter (12637 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12637 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12637 : Reach 12637 125092967984892 168372813950 := by
  have hr := row_12637
  have hl := log_bounds hr.1
    (by change logScale (12637 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12619) (T := 124998524141949) (U := 168359490153)
    (by norm_num) (by norm_num) hr.1 gap_12637
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12619

theorem gap_12641 : PrimeGap 12637 12641 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12641 :
    (12641 : ℕ).Prime ∧ logScale (12641 : ℚ) = 13 ∧
      (94447007751 : ℤ) = ⌊logCenter (12641 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12641 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12641 : Reach 12641 125187414992643 168386134585 := by
  have hr := row_12641
  have hl := log_bounds hr.1
    (by change logScale (12641 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12637) (T := 125092967984892) (U := 168372813950)
    (by norm_num) (by norm_num) hr.1 gap_12641
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12637

theorem gap_12647 : PrimeGap 12641 12647 :=
  (primeGap_of_factors (ds := [2, 47, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12647 :
    (12647 : ℕ).Prime ∧ logScale (12647 : ℚ) = 13 ∧
      (94451753085 : ℤ) = ⌊logCenter (12647 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12647 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12647 : Reach 12647 125281866745728 168399449953 := by
  have hr := row_12647
  have hl := log_bounds hr.1
    (by change logScale (12647 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12641) (T := 125187414992643) (U := 168386134585)
    (by norm_num) (by norm_num) hr.1 gap_12647
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12641

theorem gap_12653 : PrimeGap 12647 12653 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12653 :
    (12653 : ℕ).Prime ∧ logScale (12653 : ℚ) = 13 ∧
      (94456496168 : ℤ) = ⌊logCenter (12653 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12653 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12653 : Reach 12653 125376323241896 168412760059 := by
  have hr := row_12653
  have hl := log_bounds hr.1
    (by change logScale (12653 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12647) (T := 125281866745728) (U := 168399449953)
    (by norm_num) (by norm_num) hr.1 gap_12653
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12647

theorem gap_12659 : PrimeGap 12653 12659 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12659 :
    (12659 : ℕ).Prime ∧ logScale (12659 : ℚ) = 13 ∧
      (94461237002 : ℤ) = ⌊logCenter (12659 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12659 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12659 : Reach 12659 125470784478898 168426064907 := by
  have hr := row_12659
  have hl := log_bounds hr.1
    (by change logScale (12659 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12653) (T := 125376323241896) (U := 168412760059)
    (by norm_num) (by norm_num) hr.1 gap_12659
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12653

theorem gap_12671 : PrimeGap 12659 12671 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 53, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12671 :
    (12671 : ℕ).Prime ∧ logScale (12671 : ℚ) = 13 ∧
      (94470711934 : ℤ) = ⌊logCenter (12671 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12671 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12671 : Reach 12671 125565255190832 168439358204 := by
  have hr := row_12671
  have hl := log_bounds hr.1
    (by change logScale (12671 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12659) (T := 125470784478898) (U := 168426064907)
    (by norm_num) (by norm_num) hr.1 gap_12671
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12659

theorem gap_12689 : PrimeGap 12671 12689 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 7, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12689 :
    (12689 : ℕ).Prime ∧ logScale (12689 : ℚ) = 13 ∧
      (94484907520 : ℤ) = ⌊logCenter (12689 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12689 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12689 : Reach 12689 125659740098352 168452633690 := by
  have hr := row_12689
  have hl := log_bounds hr.1
    (by change logScale (12689 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12671) (T := 125565255190832) (U := 168439358204)
    (by norm_num) (by norm_num) hr.1 gap_12689
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12671

theorem gap_12697 : PrimeGap 12689 12697 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12697 :
    (12697 : ℕ).Prime ∧ logScale (12697 : ℚ) = 13 ∧
      (94491210206 : ℤ) = ⌊logCenter (12697 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12697 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12697 : Reach 12697 125754231308558 168465901856 := by
  have hr := row_12697
  have hl := log_bounds hr.1
    (by change logScale (12697 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12689) (T := 125659740098352) (U := 168452633690)
    (by norm_num) (by norm_num) hr.1 gap_12697
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12689

#print axioms reach_12697

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
