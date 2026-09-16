import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block011

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3529 :
    (3529 : ℕ).Prime ∧ logScale (3529 : ℚ) = 11 ∧
      (81687698208 : ℤ) = ⌊logCenter (3529 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3529 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3529 : Reach 3529 34421231758320 145713935248 := by
  have hr := row_3529
  have hl := log_bounds hr.1
    (by change logScale (3529 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3527) (T := 34339544060112) (U := 145672644815)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3527

theorem row_3533 :
    (3533 : ℕ).Prime ∧ logScale (3533 : ℚ) = 11 ∧
      (81699026444 : ℤ) = ⌊logCenter (3533 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3533 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3533 : Reach 3533 34502930784764 145755190610 := by
  have hr := row_3533
  have hl := log_bounds hr.1
    (by change logScale (3533 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3529) (T := 34421231758320) (U := 145713935248)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3529

theorem row_3539 :
    (3539 : ℕ).Prime ∧ logScale (3539 : ℚ) = 11 ∧
      (81715994774 : ℤ) = ⌊logCenter (3539 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3539 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3539 : Reach 3539 34584646779538 145796387668 := by
  have hr := row_3539
  have hl := log_bounds hr.1
    (by change logScale (3539 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3533) (T := 34502930784764) (U := 145755190610)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3533

theorem row_3541 :
    (3541 : ℕ).Prime ∧ logScale (3541 : ℚ) = 11 ∧
      (81721644492 : ℤ) = ⌊logCenter (3541 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3541 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3541 : Reach 3541 34666368424030 145837573089 := by
  have hr := row_3541
  have hl := log_bounds hr.1
    (by change logScale (3541 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3539) (T := 34584646779538) (U := 145796387668)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3539

theorem row_3547 :
    (3547 : ℕ).Prime ∧ logScale (3547 : ℚ) = 11 ∧
      (81738574519 : ℤ) = ⌊logCenter (3547 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3547 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3547 : Reach 3547 34748106998549 145878700437 := by
  have hr := row_3547
  have hl := log_bounds hr.1
    (by change logScale (3547 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3541) (T := 34666368424030) (U := 145837573089)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3541

theorem row_3557 :
    (3557 : ℕ).Prime ∧ logScale (3557 : ℚ) = 11 ∧
      (81766727690 : ℤ) = ⌊logCenter (3557 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3557 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3557 : Reach 3557 34829873726239 145919723694 := by
  have hr := row_3557
  have hl := log_bounds hr.1
    (by change logScale (3557 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3547) (T := 34748106998549) (U := 145878700437)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3547

theorem row_3559 :
    (3559 : ℕ).Prime ∧ logScale (3559 : ℚ) = 11 ∧
      (81772348826 : ℤ) = ⌊logCenter (3559 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3559 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3559 : Reach 3559 34911646075065 145960735421 := by
  have hr := row_3559
  have hl := log_bounds hr.1
    (by change logScale (3559 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3557) (T := 34829873726239) (U := 145919723694)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3557

theorem row_3571 :
    (3571 : ℕ).Prime ∧ logScale (3571 : ℚ) = 11 ∧
      (81806009447 : ℤ) = ⌊logCenter (3571 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3571 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3571 : Reach 3571 34993452084512 146001620782 := by
  have hr := row_3571
  have hl := log_bounds hr.1
    (by change logScale (3571 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3559) (T := 34911646075065) (U := 145960735421)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3559

#print axioms reach_3571

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
