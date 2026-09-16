import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0450
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10601 : PrimeGap 10597 10601 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10601 :
    (10601 : ℕ).Prime ∧ logScale (10601 : ℚ) = 13 ∧
      (92687036118 : ℤ) = ⌊logCenter (10601 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10601 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10601 : Reach 10601 104872854304338 165269768059 := by
  have hr := row_10601
  have hl := log_bounds hr.1
    (by change logScale (10601 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10597) (T := 104780167268220) (U := 165254178042)
    (by norm_num) (by norm_num) hr.1 gap_10601
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10597

theorem gap_10607 : PrimeGap 10601 10607 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10607 :
    (10607 : ℕ).Prime ∧ logScale (10607 : ℚ) = 13 ∧
      (92692694361 : ℤ) = ⌊logCenter (10607 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10607 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10607 : Reach 10607 104965546998699 165285350727 := by
  have hr := row_10607
  have hl := log_bounds hr.1
    (by change logScale (10607 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10601) (T := 104872854304338) (U := 165269768059)
    (by norm_num) (by norm_num) hr.1 gap_10607
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10601

theorem gap_10613 : PrimeGap 10607 10613 :=
  (primeGap_of_factors (ds := [2, 103, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10613 :
    (10613 : ℕ).Prime ∧ logScale (10613 : ℚ) = 13 ∧
      (92698349403 : ℤ) = ⌊logCenter (10613 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10613 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10613 : Reach 10613 105058245348102 165300926053 := by
  have hr := row_10613
  have hl := log_bounds hr.1
    (by change logScale (10613 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10607) (T := 104965546998699) (U := 165285350727)
    (by norm_num) (by norm_num) hr.1 gap_10613
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10607

theorem gap_10627 : PrimeGap 10613 10627 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10627 :
    (10627 : ℕ).Prime ∧ logScale (10627 : ℚ) = 13 ∧
      (92711532079 : ℤ) = ⌊logCenter (10627 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10627 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10627 : Reach 10627 105150956880181 165316482324 := by
  have hr := row_10627
  have hl := log_bounds hr.1
    (by change logScale (10627 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10613) (T := 105058245348102) (U := 165300926053)
    (by norm_num) (by norm_num) hr.1 gap_10627
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10613

theorem gap_10631 : PrimeGap 10627 10631 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10631 :
    (10631 : ℕ).Prime ∧ logScale (10631 : ℚ) = 13 ∧
      (92715295369 : ℤ) = ⌊logCenter (10631 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10631 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10631 : Reach 10631 105243672175550 165332034204 := by
  have hr := row_10631
  have hl := log_bounds hr.1
    (by change logScale (10631 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10627) (T := 105150956880181) (U := 165316482324)
    (by norm_num) (by norm_num) hr.1 gap_10631
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10627

theorem gap_10639 : PrimeGap 10631 10639 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10639 :
    (10639 : ℕ).Prime ∧ logScale (10639 : ℚ) = 13 ∧
      (92722817701 : ℤ) = ⌊logCenter (10639 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10639 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10639 : Reach 10639 105336394993251 165347575851 := by
  have hr := row_10639
  have hl := log_bounds hr.1
    (by change logScale (10639 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10631) (T := 105243672175550) (U := 165332034204)
    (by norm_num) (by norm_num) hr.1 gap_10639
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10631

theorem gap_10651 : PrimeGap 10639 10651 :=
  (primeGap_of_factors (ds := [2, 3, 2, 29, 2, 5, 2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10651 :
    (10651 : ℕ).Prime ∧ logScale (10651 : ℚ) = 13 ∧
      (92734090600 : ℤ) = ⌊logCenter (10651 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10651 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10651 : Reach 10651 105429129083851 165363101445 := by
  have hr := row_10651
  have hl := log_bounds hr.1
    (by change logScale (10651 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10639) (T := 105336394993251) (U := 165347575851)
    (by norm_num) (by norm_num) hr.1 gap_10651
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10639

theorem gap_10657 : PrimeGap 10651 10657 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10657 :
    (10657 : ℕ).Prime ∧ logScale (10657 : ℚ) = 13 ∧
      (92739722288 : ℤ) = ⌊logCenter (10657 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10657 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10657 : Reach 10657 105521868806139 165378619755 := by
  have hr := row_10657
  have hl := log_bounds hr.1
    (by change logScale (10657 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10651) (T := 105429129083851) (U := 165363101445)
    (by norm_num) (by norm_num) hr.1 gap_10657
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10651

#print axioms reach_10657

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
