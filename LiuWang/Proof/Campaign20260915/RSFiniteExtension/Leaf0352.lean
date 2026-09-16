import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0351
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8513 : PrimeGap 8501 8513 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 47, 2, 67, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8513 :
    (8513 : ℕ).Prime ∧ logScale (8513 : ℚ) = 13 ∧
      (90493496825 : ℤ) = ⌊logCenter (8513 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8513 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8513 : Reach 8513 83620969491302 161279468137 := by
  have hr := row_8513
  have hl := log_bounds hr.1
    (by change logScale (8513 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8501) (T := 83530475994477) (U := 161260523056)
    (by norm_num) (by norm_num) hr.1 gap_8513
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8501

theorem gap_8521 : PrimeGap 8513 8521 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8521 :
    (8521 : ℕ).Prime ∧ logScale (8521 : ℚ) = 13 ∧
      (90502889804 : ℤ) = ⌊logCenter (8521 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8521 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8521 : Reach 8521 83711472381106 161298397653 := by
  have hr := row_8521
  have hl := log_bounds hr.1
    (by change logScale (8521 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8513) (T := 83620969491302) (U := 161279468137)
    (by norm_num) (by norm_num) hr.1 gap_8521
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8513

theorem gap_8527 : PrimeGap 8521 8527 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8527 :
    (8527 : ℕ).Prime ∧ logScale (8527 : ℚ) = 13 ∧
      (90509928753 : ℤ) = ⌊logCenter (8527 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8527 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8527 : Reach 8527 83801982309859 161317316067 := by
  have hr := row_8527
  have hl := log_bounds hr.1
    (by change logScale (8527 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8521) (T := 83711472381106) (U := 161298397653)
    (by norm_num) (by norm_num) hr.1 gap_8527
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8521

theorem gap_8537 : PrimeGap 8527 8537 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8537 :
    (8537 : ℕ).Prime ∧ logScale (8537 : ℚ) = 13 ∧
      (90521649336 : ℤ) = ⌊logCenter (8537 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8537 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8537 : Reach 8537 83892503959195 161336214535 := by
  have hr := row_8537
  have hl := log_bounds hr.1
    (by change logScale (8537 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8527) (T := 83801982309859) (U := 161317316067)
    (by norm_num) (by norm_num) hr.1 gap_8537
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8527

theorem gap_8539 : PrimeGap 8537 8539 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8539 :
    (8539 : ℕ).Prime ∧ logScale (8539 : ℚ) = 13 ∧
      (90523991805 : ℤ) = ⌊logCenter (8539 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8539 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8539 : Reach 8539 83983027951000 161355110789 := by
  have hr := row_8539
  have hl := log_bounds hr.1
    (by change logScale (8539 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8537) (T := 83892503959195) (U := 161336214535)
    (by norm_num) (by norm_num) hr.1 gap_8539
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8537

theorem gap_8543 : PrimeGap 8539 8543 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8543 :
    (8543 : ℕ).Prime ∧ logScale (8543 : ℚ) = 13 ∧
      (90528675097 : ℤ) = ⌊logCenter (8543 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8543 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8543 : Reach 8543 84073556626097 161374000407 := by
  have hr := row_8543
  have hl := log_bounds hr.1
    (by change logScale (8543 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8539) (T := 83983027951000) (U := 161355110789)
    (by norm_num) (by norm_num) hr.1 gap_8543
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8539

theorem gap_8563 : PrimeGap 8543 8563 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 83, 2, 17, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8563 :
    (8563 : ℕ).Prime ∧ logScale (8563 : ℚ) = 13 ∧
      (90552058716 : ℤ) = ⌊logCenter (8563 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8563 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8563 : Reach 8563 84164108684813 161392848107 := by
  have hr := row_8563
  have hl := log_bounds hr.1
    (by change logScale (8563 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8543) (T := 84073556626097) (U := 161374000407)
    (by norm_num) (by norm_num) hr.1 gap_8563
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8543

theorem gap_8573 : PrimeGap 8563 8573 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8573 :
    (8573 : ℕ).Prime ∧ logScale (8573 : ℚ) = 13 ∧
      (90563730052 : ℤ) = ⌊logCenter (8573 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8573 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8573 : Reach 8573 84254672414865 161411676018 := by
  have hr := row_8573
  have hl := log_bounds hr.1
    (by change logScale (8573 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8563) (T := 84164108684813) (U := 161392848107)
    (by norm_num) (by norm_num) hr.1 gap_8573
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8563

#print axioms reach_8573

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
