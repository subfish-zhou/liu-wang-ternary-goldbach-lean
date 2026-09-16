import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block061
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14437 : PrimeGap 14431 14437 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14437 :
    (14437 : ℕ).Prime ∧ logScale (14437 : ℚ) = 13 ∧
      (95775496312 : ℤ) = ⌊logCenter (14437 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14437 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14437 : Reach 14437 142593865652230 170683066251 := by
  have hr := row_14437
  have hl := log_bounds hr.1
    (by change logScale (14437 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14431) (T := 142498090155918) (U := 170671243637)
    (by norm_num) (by norm_num) hr.1 gap_14437
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14431

theorem gap_14447 : PrimeGap 14437 14447 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14447 :
    (14447 : ℕ).Prime ∧ logScale (14447 : ℚ) = 13 ∧
      (95782420561 : ℤ) = ⌊logCenter (14447 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14447 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14447 : Reach 14447 142689648072791 170694881499 := by
  have hr := row_14447
  have hl := log_bounds hr.1
    (by change logScale (14447 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14437) (T := 142593865652230) (U := 170683066251)
    (by norm_num) (by norm_num) hr.1 gap_14447
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14437

theorem gap_14449 : PrimeGap 14447 14449 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14449 :
    (14449 : ℕ).Prime ∧ logScale (14449 : ℚ) = 13 ∧
      (95783804836 : ℤ) = ⌊logCenter (14449 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14449 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14449 : Reach 14449 142785431877627 170706695929 := by
  have hr := row_14449
  have hl := log_bounds hr.1
    (by change logScale (14449 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14447) (T := 142689648072791) (U := 170694881499)
    (by norm_num) (by norm_num) hr.1 gap_14449
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14447

theorem gap_14461 : PrimeGap 14449 14461 :=
  (primeGap_of_factors (ds := [2, 3, 2, 97, 2, 5, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14461 :
    (14461 : ℕ).Prime ∧ logScale (14461 : ℚ) = 13 ∧
      (95792106462 : ℤ) = ⌊logCenter (14461 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14461 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14461 : Reach 14461 142881223984089 170718501372 := by
  have hr := row_14461
  have hl := log_bounds hr.1
    (by change logScale (14461 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14449) (T := 142785431877627) (U := 170706695929)
    (by norm_num) (by norm_num) hr.1 gap_14461
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14449

theorem gap_14479 : PrimeGap 14461 14479 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 17, 2, 3, 2, 29, 2, 41, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14479 :
    (14479 : ℕ).Prime ∧ logScale (14479 : ℚ) = 13 ∧
      (95804545994 : ℤ) = ⌊logCenter (14479 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14479 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14479 : Reach 14479 142977028530083 170730292953 := by
  have hr := row_14479
  have hl := log_bounds hr.1
    (by change logScale (14479 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14461) (T := 142881223984089) (U := 170718501372)
    (by norm_num) (by norm_num) hr.1 gap_14479
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14461

theorem gap_14489 : PrimeGap 14479 14489 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14489 :
    (14489 : ℕ).Prime ∧ logScale (14489 : ℚ) = 13 ∧
      (95811450164 : ℤ) = ⌊logCenter (14489 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14489 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14489 : Reach 14489 143072839980247 170742077209 := by
  have hr := row_14489
  have hl := log_bounds hr.1
    (by change logScale (14489 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14479) (T := 142977028530083) (U := 170730292953)
    (by norm_num) (by norm_num) hr.1 gap_14489
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14479

theorem gap_14503 : PrimeGap 14489 14503 :=
  (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14503 :
    (14503 : ℕ).Prime ∧ logScale (14503 : ℚ) = 13 ∧
      (95821108001 : ℤ) = ⌊logCenter (14503 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14503 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14503 : Reach 14503 143168661088248 170753850901 := by
  have hr := row_14503
  have hl := log_bounds hr.1
    (by change logScale (14503 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14489) (T := 143072839980247) (U := 170742077209)
    (by norm_num) (by norm_num) hr.1 gap_14503
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14489

theorem gap_14519 : PrimeGap 14503 14519 :=
  (primeGap_of_factors (ds := [2, 3, 2, 89, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14519 :
    (14519 : ℕ).Prime ∧ logScale (14519 : ℚ) = 13 ∧
      (95832134121 : ℤ) = ⌊logCenter (14519 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14519 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14519 : Reach 14519 143264493222369 170765612429 := by
  have hr := row_14519
  have hl := log_bounds hr.1
    (by change logScale (14519 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14503) (T := 143168661088248) (U := 170753850901)
    (by norm_num) (by norm_num) hr.1 gap_14519
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14503

#print axioms reach_14519

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
