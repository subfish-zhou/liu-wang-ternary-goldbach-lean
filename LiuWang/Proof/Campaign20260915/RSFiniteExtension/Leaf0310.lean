import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block030
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7489 : PrimeGap 7487 7489 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7489 :
    (7489 : ℕ).Prime ∧ logScale (7489 : ℚ) = 12 ∧
      (89211905531 : ℤ) = ⌊logCenter (7489 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7489 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7489 : Reach 7489 73559348883886 159027539798 := by
  have hr := row_7489
  have hl := log_bounds hr.1
    (by change logScale (7489 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7487) (T := 73470136978355) (U := 159006304981)
    (by norm_num) (by norm_num) hr.1 gap_7489
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7487

theorem gap_7499 : PrimeGap 7489 7499 :=
  (primeGap_of_factors (ds := [2, 3, 2, 59, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7499 :
    (7499 : ℕ).Prime ∧ logScale (7499 : ℚ) = 12 ∧
      (89225249541 : ℤ) = ⌊logCenter (7499 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7499 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7499 : Reach 7499 73648574133427 159048749126 := by
  have hr := row_7499
  have hl := log_bounds hr.1
    (by change logScale (7499 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7489) (T := 73559348883886) (U := 159027539798)
    (by norm_num) (by norm_num) hr.1 gap_7499
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7489

theorem gap_7507 : PrimeGap 7499 7507 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7507 :
    (7507 : ℕ).Prime ∧ logScale (7507 : ℚ) = 12 ∧
      (89235911944 : ℤ) = ⌊logCenter (7507 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7507 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7507 : Reach 7507 73737810045371 159069938675 := by
  have hr := row_7507
  have hl := log_bounds hr.1
    (by change logScale (7507 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7499) (T := 73648574133427) (U := 159048749126)
    (by norm_num) (by norm_num) hr.1 gap_7507
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7499

theorem gap_7517 : PrimeGap 7507 7517 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7517 :
    (7517 : ℕ).Prime ∧ logScale (7517 : ℚ) = 12 ∧
      (89249223980 : ℤ) = ⌊logCenter (7517 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7517 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7517 : Reach 7517 73827059269351 159091102850 := by
  have hr := row_7517
  have hl := log_bounds hr.1
    (by change logScale (7517 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7507) (T := 73737810045371) (U := 159069938675)
    (by norm_num) (by norm_num) hr.1 gap_7517
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7507

theorem gap_7523 : PrimeGap 7517 7523 :=
  (primeGap_of_factors (ds := [2, 73, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7523 :
    (7523 : ℕ).Prime ∧ logScale (7523 : ℚ) = 12 ∧
      (89257202704 : ℤ) = ⌊logCenter (7523 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7523 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7523 : Reach 7523 73916316472055 159112252957 := by
  have hr := row_7523
  have hl := log_bounds hr.1
    (by change logScale (7523 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7517) (T := 73827059269351) (U := 159091102850)
    (by norm_num) (by norm_num) hr.1 gap_7523
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7517

theorem gap_7529 : PrimeGap 7523 7529 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7529 :
    (7529 : ℕ).Prime ∧ logScale (7529 : ℚ) = 12 ∧
      (89265175067 : ℤ) = ⌊logCenter (7529 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7529 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7529 : Reach 7529 74005581647122 159133389017 := by
  have hr := row_7529
  have hl := log_bounds hr.1
    (by change logScale (7529 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7523) (T := 73916316472055) (U := 159112252957)
    (by norm_num) (by norm_num) hr.1 gap_7529
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7523

theorem gap_7537 : PrimeGap 7529 7537 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7537 :
    (7537 : ℕ).Prime ∧ logScale (7537 : ℚ) = 12 ∧
      (89275795007 : ℤ) = ⌊logCenter (7537 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7537 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7537 : Reach 7537 74094857442129 159154505444 := by
  have hr := row_7537
  have hl := log_bounds hr.1
    (by change logScale (7537 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7529) (T := 74005581647122) (U := 159133389017)
    (by norm_num) (by norm_num) hr.1 gap_7537
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7529

theorem gap_7541 : PrimeGap 7537 7541 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7541 :
    (7541 : ℕ).Prime ∧ logScale (7541 : ℚ) = 12 ∧
      (89281100750 : ℤ) = ⌊logCenter (7541 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7541 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7541 : Reach 7541 74184138542879 159175613469 := by
  have hr := row_7541
  have hl := log_bounds hr.1
    (by change logScale (7541 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7537) (T := 74094857442129) (U := 159154505444)
    (by norm_num) (by norm_num) hr.1 gap_7541
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7537

#print axioms reach_7541

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
