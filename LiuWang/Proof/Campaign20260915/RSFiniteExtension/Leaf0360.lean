import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block035
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8581 : PrimeGap 8573 8581 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8581 :
    (8581 : ℕ).Prime ∧ logScale (8581 : ℚ) = 13 ∧
      (90573057324 : ℤ) = ⌊logCenter (8581 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8581 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8581 : Reach 8581 84345245472189 161430488568 := by
  have hr := row_8581
  have hl := log_bounds hr.1
    (by change logScale (8581 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8573) (T := 84254672414865) (U := 161411676018)
    (by norm_num) (by norm_num) hr.1 gap_8581
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8573

theorem gap_8597 : PrimeGap 8581 8597 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8597 :
    (8597 : ℕ).Prime ∧ logScale (8597 : ℚ) = 13 ∧
      (90591685807 : ℤ) = ⌊logCenter (8597 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8597 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8597 : Reach 8597 84435837157996 161449268290 := by
  have hr := row_8597
  have hl := log_bounds hr.1
    (by change logScale (8597 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8581) (T := 84345245472189) (U := 161430488568)
    (by norm_num) (by norm_num) hr.1 gap_8597
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8581

theorem gap_8599 : PrimeGap 8597 8599 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8599 :
    (8599 : ℕ).Prime ∧ logScale (8599 : ℚ) = 13 ∧
      (90594011930 : ℤ) = ⌊logCenter (8599 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8599 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8599 : Reach 8599 84526431169926 161468045828 := by
  have hr := row_8599
  have hl := log_bounds hr.1
    (by change logScale (8599 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8597) (T := 84435837157996) (U := 161449268290)
    (by norm_num) (by norm_num) hr.1 gap_8599
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8597

theorem gap_8609 : PrimeGap 8599 8609 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8609 :
    (8609 : ℕ).Prime ∧ logScale (8609 : ℚ) = 13 ∧
      (90605634432 : ℤ) = ⌊logCenter (8609 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8609 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8609 : Reach 8609 84617036804358 161486803733 := by
  have hr := row_8609
  have hl := log_bounds hr.1
    (by change logScale (8609 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8599) (T := 84526431169926) (U := 161468045828)
    (by norm_num) (by norm_num) hr.1 gap_8609
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8599

theorem gap_8623 : PrimeGap 8609 8623 :=
  (primeGap_of_factors (ds := [2, 79, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8623 :
    (8623 : ℕ).Prime ∧ logScale (8623 : ℚ) = 13 ∧
      (90621883275 : ℤ) = ⌊logCenter (8623 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8623 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8623 : Reach 8623 84707658687633 161505533356 := by
  have hr := row_8623
  have hl := log_bounds hr.1
    (by change logScale (8623 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8609) (T := 84617036804358) (U := 161486803733)
    (by norm_num) (by norm_num) hr.1 gap_8623
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8609

theorem gap_8627 : PrimeGap 8623 8627 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8627 :
    (8627 : ℕ).Prime ∧ logScale (8627 : ℚ) = 13 ∧
      (90626520956 : ℤ) = ⌊logCenter (8627 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8627 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8627 : Reach 8627 84798285208589 161524256465 := by
  have hr := row_8627
  have hl := log_bounds hr.1
    (by change logScale (8627 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8623) (T := 84707658687633) (U := 161505533356)
    (by norm_num) (by norm_num) hr.1 gap_8627
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8623

theorem gap_8629 : PrimeGap 8627 8629 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8629 :
    (8629 : ℕ).Prime ∧ logScale (8629 : ℚ) = 13 ∧
      (90628838991 : ℤ) = ⌊logCenter (8629 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8629 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8629 : Reach 8629 84888914047580 161542977404 := by
  have hr := row_8629
  have hl := log_bounds hr.1
    (by change logScale (8629 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8627) (T := 84798285208589) (U := 161524256465)
    (by norm_num) (by norm_num) hr.1 gap_8629
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8627

theorem gap_8641 : PrimeGap 8629 8641 :=
  (primeGap_of_factors (ds := [2, 3, 2, 89, 2, 5, 2, 3, 2, 53, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8641 :
    (8641 : ℕ).Prime ∧ logScale (8641 : ℚ) = 13 ∧
      (90642735924 : ℤ) = ⌊logCenter (8641 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8641 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8641 : Reach 8641 84979556783504 161561674508 := by
  have hr := row_8641
  have hl := log_bounds hr.1
    (by change logScale (8641 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8629) (T := 84888914047580) (U := 161542977404)
    (by norm_num) (by norm_num) hr.1 gap_8641
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8629

#print axioms reach_8641

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
