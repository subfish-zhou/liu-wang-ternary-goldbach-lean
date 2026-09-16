import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0670
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15619 : PrimeGap 15607 15619 :=
  (primeGap_of_factors (ds := [2, 3, 2, 67, 2, 13, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15619 :
    (15619 : ℕ).Prime ∧ logScale (15619 : ℚ) = 13 ∧
      (96562433974 : ℤ) = ⌊logCenter (15619 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15619 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15619 : Reach 15619 154904212991195 172143785871 := by
  have hr := row_15619
  have hl := log_bounds hr.1
    (by change logScale (15619 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15607) (T := 154807650557221) (U := 172132764436)
    (by norm_num) (by norm_num) hr.1 gap_15619
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15607

theorem gap_15629 : PrimeGap 15619 15629 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15629 :
    (15629 : ℕ).Prime ∧ logScale (15629 : ℚ) = 13 ∧
      (96568834384 : ℤ) = ⌊logCenter (15629 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15629 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15629 : Reach 15629 155000781825579 172154800959 := by
  have hr := row_15629
  have hl := log_bounds hr.1
    (by change logScale (15629 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15619) (T := 154904212991195) (U := 172143785871)
    (by norm_num) (by norm_num) hr.1 gap_15629
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15619

theorem gap_15641 : PrimeGap 15629 15641 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15641 :
    (15641 : ℕ).Prime ∧ logScale (15641 : ℚ) = 13 ∧
      (96576509472 : ℤ) = ⌊logCenter (15641 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15641 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15641 : Reach 15641 155097358335051 172165808300 := by
  have hr := row_15641
  have hl := log_bounds hr.1
    (by change logScale (15641 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15629) (T := 155000781825579) (U := 172154800959)
    (by norm_num) (by norm_num) hr.1 gap_15641
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15629

theorem gap_15643 : PrimeGap 15641 15643 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15643 :
    (15643 : ℕ).Prime ∧ logScale (15643 : ℚ) = 13 ∧
      (96577788081 : ℤ) = ⌊logCenter (15643 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15643 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15643 : Reach 15643 155193936123132 172176814937 := by
  have hr := row_15643
  have hl := log_bounds hr.1
    (by change logScale (15643 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15641) (T := 155097358335051) (U := 172165808300)
    (by norm_num) (by norm_num) hr.1 gap_15643
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15641

theorem gap_15647 : PrimeGap 15643 15647 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15647 :
    (15647 : ℕ).Prime ∧ logScale (15647 : ℚ) = 13 ∧
      (96580344809 : ℤ) = ⌊logCenter (15647 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15647 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15647 : Reach 15647 155290516467941 172187819464 := by
  have hr := row_15647
  have hl := log_bounds hr.1
    (by change logScale (15647 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15643) (T := 155193936123132) (U := 172176814937)
    (by norm_num) (by norm_num) hr.1 gap_15647
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15643

theorem gap_15649 : PrimeGap 15647 15649 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15649 :
    (15649 : ℕ).Prime ∧ logScale (15649 : ℚ) = 13 ∧
      (96581622927 : ℤ) = ⌊logCenter (15649 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15649 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15649 : Reach 15649 155387098090868 172198823287 := by
  have hr := row_15649
  have hl := log_bounds hr.1
    (by change logScale (15649 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15647) (T := 155290516467941) (U := 172187819464)
    (by norm_num) (by norm_num) hr.1 gap_15649
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15647

theorem gap_15661 : PrimeGap 15649 15661 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15661 :
    (15661 : ℕ).Prime ∧ logScale (15661 : ℚ) = 13 ∧
      (96589288210 : ℤ) = ⌊logCenter (15661 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15661 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15661 : Reach 15661 155483687379078 172209819381 := by
  have hr := row_15661
  have hl := log_bounds hr.1
    (by change logScale (15661 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15649) (T := 155387098090868) (U := 172198823287)
    (by norm_num) (by norm_num) hr.1 gap_15661
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15649

theorem gap_15667 : PrimeGap 15661 15667 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15667 :
    (15667 : ℕ).Prime ∧ logScale (15667 : ℚ) = 13 ∧
      (96593118650 : ℤ) = ⌊logCenter (15667 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15667 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15667 : Reach 15667 155580280497728 172220811965 := by
  have hr := row_15667
  have hl := log_bounds hr.1
    (by change logScale (15667 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15661) (T := 155483687379078) (U := 172209819381)
    (by norm_num) (by norm_num) hr.1 gap_15667
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15661

#print axioms reach_15667

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
