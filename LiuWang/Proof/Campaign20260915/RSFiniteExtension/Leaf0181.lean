import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0180

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4793 :
    (4793 : ℕ).Prime ∧ logScale (4793 : ℚ) = 12 ∧
      (84749117960 : ℤ) = ⌊logCenter (4793 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4793 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4793 : Reach 4793 47077226048345 151198263918 := by
  have hr := row_4793
  have hl := log_bounds hr.1
    (by change logScale (4793 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4789) (T := 46992476930385) (U := 151166718275)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4789

theorem row_4799 :
    (4799 : ℕ).Prime ∧ logScale (4799 : ℚ) = 12 ∧
      (84761628387 : ℤ) = ⌊logCenter (4799 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4799 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4799 : Reach 4799 47161987676732 151229776687 := by
  have hr := row_4799
  have hl := log_bounds hr.1
    (by change logScale (4799 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4793) (T := 47077226048345) (U := 151198263918)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4793

theorem row_4801 :
    (4801 : ℕ).Prime ∧ logScale (4801 : ℚ) = 12 ∧
      (84765795054 : ℤ) = ⌊logCenter (4801 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4801 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4801 : Reach 4801 47246753471786 151261282891 := by
  have hr := row_4801
  have hl := log_bounds hr.1
    (by change logScale (4801 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4799) (T := 47161987676732) (U := 151229776687)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4799

theorem row_4813 :
    (4813 : ℕ).Prime ∧ logScale (4813 : ℚ) = 12 ∧
      (84790758661 : ℤ) = ⌊logCenter (4813 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4813 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4813 : Reach 4813 47331544230447 151292717073 := by
  have hr := row_4813
  have hl := log_bounds hr.1
    (by change logScale (4813 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4801) (T := 47246753471786) (U := 151261282891)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4801

theorem row_4817 :
    (4817 : ℕ).Prime ∧ logScale (4817 : ℚ) = 12 ∧
      (84799066035 : ℤ) = ⌊logCenter (4817 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4817 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4817 : Reach 4817 47416343296482 151324131674 := by
  have hr := row_4817
  have hl := log_bounds hr.1
    (by change logScale (4817 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4813) (T := 47331544230447) (U := 151292717073)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4813

theorem row_4831 :
    (4831 : ℕ).Prime ∧ logScale (4831 : ℚ) = 12 ∧
      (84828087614 : ℤ) = ⌊logCenter (4831 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4831 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4831 : Reach 4831 47501171384096 151355461722 := by
  have hr := row_4831
  have hl := log_bounds hr.1
    (by change logScale (4831 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4817) (T := 47416343296482) (U := 151324131674)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4817

theorem row_4861 :
    (4861 : ℕ).Prime ∧ logScale (4861 : ℚ) = 12 ∧
      (84889994539 : ℤ) = ⌊logCenter (4861 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4861 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4861 : Reach 4861 47586061378635 151386604822 := by
  have hr := row_4861
  have hl := log_bounds hr.1
    (by change logScale (4861 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4831) (T := 47501171384096) (U := 151355461722)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4831

theorem row_4871 :
    (4871 : ℕ).Prime ∧ logScale (4871 : ℚ) = 12 ∧
      (84910545306 : ℤ) = ⌊logCenter (4871 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4871 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4871 : Reach 4871 47670971923941 151417690368 := by
  have hr := row_4871
  have hl := log_bounds hr.1
    (by change logScale (4871 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4861) (T := 47586061378635) (U := 151386604822)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4861

#print axioms reach_4871

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
