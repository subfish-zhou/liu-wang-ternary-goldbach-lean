import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0211

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5483 :
    (5483 : ℕ).Prime ∧ logScale (5483 : ℚ) = 12 ∧
      (86094076722 : ℤ) = ⌊logCenter (5483 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5483 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5483 : Reach 5483 53913722363851 153570102120 := by
  have hr := row_5483
  have hl := log_bounds hr.1
    (by change logScale (5483 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5479) (T := 53827628287129) (U := 153542093711)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5479

theorem row_5501 :
    (5501 : ℕ).Prime ∧ logScale (5501 : ℚ) = 12 ∧
      (86126851697 : ℤ) = ⌊logCenter (5501 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5501 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5501 : Reach 5501 53999849215548 153598023957 := by
  have hr := row_5501
  have hl := log_bounds hr.1
    (by change logScale (5501 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5483) (T := 53913722363851) (U := 153570102120)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5483

theorem row_5503 :
    (5503 : ℕ).Prime ∧ logScale (5503 : ℚ) = 12 ∧
      (86130486739 : ℤ) = ⌊logCenter (5503 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5503 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5503 : Reach 5503 54085979702287 153625940719 := by
  have hr := row_5503
  have hl := log_bounds hr.1
    (by change logScale (5503 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5501) (T := 53999849215548) (U := 153598023957)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5501

theorem row_5507 :
    (5507 : ℕ).Prime ∧ logScale (5507 : ℚ) = 12 ∧
      (86137752861 : ℤ) = ⌊logCenter (5507 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5507 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5507 : Reach 5507 54172117455148 153653842271 := by
  have hr := row_5507
  have hl := log_bounds hr.1
    (by change logScale (5507 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5503) (T := 54085979702287) (U := 153625940719)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5503

theorem row_5519 :
    (5519 : ℕ).Prime ∧ logScale (5519 : ℚ) = 12 ∧
      (86159519603 : ℤ) = ⌊logCenter (5519 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5519 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5519 : Reach 5519 54258276974751 153681688202 := by
  have hr := row_5519
  have hl := log_bounds hr.1
    (by change logScale (5519 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5507) (T := 54172117455148) (U := 153653842271)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5507

theorem row_5521 :
    (5521 : ℕ).Prime ∧ logScale (5521 : ℚ) = 12 ∧
      (86163142791 : ℤ) = ⌊logCenter (5521 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5521 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5521 : Reach 5521 54344440117542 153709529088 := by
  have hr := row_5521
  have hl := log_bounds hr.1
    (by change logScale (5521 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5519) (T := 54258276974751) (U := 153681688202)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5519

theorem row_5527 :
    (5527 : ℕ).Prime ∧ logScale (5527 : ℚ) = 12 ∧
      (86174004487 : ℤ) = ⌊logCenter (5527 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5527 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5527 : Reach 5527 54430614122029 153737344783 := by
  have hr := row_5527
  have hl := log_bounds hr.1
    (by change logScale (5527 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5521) (T := 54344440117542) (U := 153709529088)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5521

theorem row_5531 :
    (5531 : ℕ).Prime ∧ logScale (5531 : ℚ) = 12 ∧
      (86181239068 : ℤ) = ⌊logCenter (5531 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5531 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5531 : Reach 5531 54516795361097 153765145388 := by
  have hr := row_5531
  have hl := log_bounds hr.1
    (by change logScale (5531 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5527) (T := 54430614122029) (U := 153737344783)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5527

#print axioms reach_5531

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
