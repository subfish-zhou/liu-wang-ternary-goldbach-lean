import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0081

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2843 :
    (2843 : ℕ).Prime ∧ logScale (2843 : ℚ) = 11 ∧
      (79526151087 : ℤ) = ⌊logCenter (2843 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2843 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2843 : Reach 2843 27967126623845 142097020939 := by
  have hr := row_2843
  have hl := log_bounds hr.1
    (by change logScale (2843 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2837) (T := 27887600472758) (U := 142047039573)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2837

theorem row_2851 :
    (2851 : ℕ).Prime ∧ logScale (2851 : ℚ) = 11 ∧
      (79554250860 : ℤ) = ⌊logCenter (2851 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2851 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2851 : Reach 2851 28046680874705 142146879543 := by
  have hr := row_2851
  have hl := log_bounds hr.1
    (by change logScale (2851 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2843) (T := 27967126623845) (U := 142097020939)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2843

theorem row_2857 :
    (2857 : ℕ).Prime ∧ logScale (2857 : ℚ) = 11 ∧
      (79575273993 : ℤ) = ⌊logCenter (2857 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2857 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2857 : Reach 2857 28126256148698 142196650860 := by
  have hr := row_2857
  have hl := log_bounds hr.1
    (by change logScale (2857 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2851) (T := 28046680874705) (U := 142146879543)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2851

theorem row_2861 :
    (2861 : ℕ).Prime ∧ logScale (2861 : ℚ) = 11 ∧
      (79589264901 : ℤ) = ⌊logCenter (2861 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2861 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2861 : Reach 2861 28205845413599 142246369969 := by
  have hr := row_2861
  have hl := log_bounds hr.1
    (by change logScale (2861 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2857) (T := 28126256148698) (U := 142196650860)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2857

theorem row_2879 :
    (2879 : ℕ).Prime ∧ logScale (2879 : ℚ) = 11 ∧
      (79651982877 : ℤ) = ⌊logCenter (2879 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2879 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2879 : Reach 2879 28285497396476 142295795393 := by
  have hr := row_2879
  have hl := log_bounds hr.1
    (by change logScale (2879 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2861) (T := 28205845413599) (U := 142246369969)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2861

theorem row_2887 :
    (2887 : ℕ).Prime ∧ logScale (2887 : ℚ) = 11 ∧
      (79679731768 : ℤ) = ⌊logCenter (2887 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2887 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2887 : Reach 2887 28365177128244 142345100936 := by
  have hr := row_2887
  have hl := log_bounds hr.1
    (by change logScale (2887 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2879) (T := 28285497396476) (U := 142295795393)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2879

theorem row_2897 :
    (2897 : ℕ).Prime ∧ logScale (2897 : ℚ) = 11 ∧
      (79714309949 : ℤ) = ⌊logCenter (2897 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2897 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2897 : Reach 2897 28444891438193 142394253250 := by
  have hr := row_2897
  have hl := log_bounds hr.1
    (by change logScale (2897 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2887) (T := 28365177128244) (U := 142345100936)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2887

theorem row_2903 :
    (2903 : ℕ).Prime ∧ logScale (2903 : ℚ) = 11 ∧
      (79734999611 : ℤ) = ⌊logCenter (2903 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2903 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2903 : Reach 2903 28524626437804 142443320877 := by
  have hr := row_2903
  have hl := log_bounds hr.1
    (by change logScale (2903 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2897) (T := 28444891438193) (U := 142394253250)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2897

#print axioms reach_2903

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
