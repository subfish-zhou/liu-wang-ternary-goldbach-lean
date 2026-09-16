import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0230

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5827 :
    (5827 : ℕ).Prime ∧ logScale (5827 : ℚ) = 12 ∧
      (86702575640 : ℤ) = ⌊logCenter (5827 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5827 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5827 : Reach 5827 57370251939781 154659355707 := by
  have hr := row_5827
  have hl := log_bounds hr.1
    (by change logScale (5827 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5821) (T := 57283549364141) (U := 154632813857)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5821

theorem row_5839 :
    (5839 : ℕ).Prime ∧ logScale (5839 : ℚ) = 12 ∧
      (86723148251 : ℤ) = ⌊logCenter (5839 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5839 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5839 : Reach 5839 57456975088032 154685847546 := by
  have hr := row_5839
  have hl := log_bounds hr.1
    (by change logScale (5839 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5827) (T := 57370251939781) (U := 154659355707)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5827

theorem row_5843 :
    (5843 : ℕ).Prime ∧ logScale (5843 : ℚ) = 12 ∧
      (86729996394 : ℤ) = ⌊logCenter (5843 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5843 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5843 : Reach 5843 57543705084426 154712325781 := by
  have hr := row_5843
  have hl := log_bounds hr.1
    (by change logScale (5843 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5839) (T := 57456975088032) (U := 154685847546)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5839

theorem row_5849 :
    (5849 : ℕ).Prime ∧ logScale (5849 : ℚ) = 12 ∧
      (86740259823 : ℤ) = ⌊logCenter (5849 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5849 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5849 : Reach 5849 57630445344249 154738781378 := by
  have hr := row_5849
  have hl := log_bounds hr.1
    (by change logScale (5849 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5843) (T := 57543705084426) (U := 154712325781)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5843

theorem row_5851 :
    (5851 : ℕ).Prime ∧ logScale (5851 : ℚ) = 12 ∧
      (86743678626 : ℤ) = ⌊logCenter (5851 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5851 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5851 : Reach 5851 57717189022875 154765232452 := by
  have hr := row_5851
  have hl := log_bounds hr.1
    (by change logScale (5851 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5849) (T := 57630445344249) (U := 154738781378)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5849

theorem row_5857 :
    (5857 : ℕ).Prime ∧ logScale (5857 : ℚ) = 12 ∧
      (86753928029 : ℤ) = ⌊logCenter (5857 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5857 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5857 : Reach 5857 57803942950904 154791660942 := by
  have hr := row_5857
  have hl := log_bounds hr.1
    (by change logScale (5857 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5851) (T := 57717189022875) (U := 154765232452)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5851

theorem row_5861 :
    (5861 : ℕ).Prime ∧ logScale (5861 : ℚ) = 12 ∧
      (86760755133 : ℤ) = ⌊logCenter (5861 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5861 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5861 : Reach 5861 57890703706037 154818075902 := by
  have hr := row_5861
  have hl := log_bounds hr.1
    (by change logScale (5861 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5857) (T := 57803942950904) (U := 154791660942)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5857

theorem row_5867 :
    (5867 : ℕ).Prime ∧ logScale (5867 : ℚ) = 12 ∧
      (86770987058 : ℤ) = ⌊logCenter (5867 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5867 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5867 : Reach 5867 57977474693095 154844468346 := by
  have hr := row_5867
  have hl := log_bounds hr.1
    (by change logScale (5867 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5861) (T := 57890703706037) (U := 154818075902)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5861

#print axioms reach_5867

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
