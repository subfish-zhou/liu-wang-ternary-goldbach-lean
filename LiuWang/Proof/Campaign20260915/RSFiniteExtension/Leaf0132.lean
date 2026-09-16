import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0131

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3847 :
    (3847 : ℕ).Prime ∧ logScale (3847 : ℚ) = 11 ∧
      (82550488998 : ℤ) = ⌊logCenter (3847 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3847 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3847 : Reach 3847 37705273135946 147308055984 := by
  have hr := row_3847
  have hl := log_bounds hr.1
    (by change logScale (3847 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3833) (T := 37622722646948) (U := 147269764313)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3833

theorem row_3851 :
    (3851 : ℕ).Prime ∧ logScale (3851 : ℚ) = 11 ∧
      (82560881309 : ℤ) = ⌊logCenter (3851 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3851 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3851 : Reach 3851 37787834017255 147346317817 := by
  have hr := row_3851
  have hl := log_bounds hr.1
    (by change logScale (3851 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3847) (T := 37705273135946) (U := 147308055984)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3847

theorem row_3853 :
    (3853 : ℕ).Prime ∧ logScale (3853 : ℚ) = 11 ∧
      (82566073417 : ℤ) = ⌊logCenter (3853 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3853 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3853 : Reach 3853 37870400090672 147384569717 := by
  have hr := row_3853
  have hl := log_bounds hr.1
    (by change logScale (3853 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3851) (T := 37787834017255) (U := 147346317817)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3851

theorem row_3863 :
    (3863 : ℕ).Prime ∧ logScale (3863 : ℚ) = 11 ∧
      (82591993598 : ℤ) = ⌊logCenter (3863 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3863 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3863 : Reach 3863 37952992084270 147422732475 := by
  have hr := row_3863
  have hl := log_bounds hr.1
    (by change logScale (3863 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3853) (T := 37870400090672) (U := 147384569717)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3853

theorem row_3877 :
    (3877 : ℕ).Prime ∧ logScale (3877 : ℚ) = 11 ∧
      (82628169348 : ℤ) = ⌊logCenter (3877 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3877 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3877 : Reach 3877 38035620253618 147460767236 := by
  have hr := row_3877
  have hl := log_bounds hr.1
    (by change logScale (3877 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3863) (T := 37952992084270) (U := 147422732475)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3863

theorem row_3881 :
    (3881 : ℕ).Prime ∧ logScale (3881 : ℚ) = 11 ∧
      (82638481285 : ℤ) = ⌊logCenter (3881 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3881 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3881 : Reach 3881 38118258734903 147498772589 := by
  have hr := row_3881
  have hl := log_bounds hr.1
    (by change logScale (3881 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3877) (T := 38035620253618) (U := 147460767236)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3877

theorem row_3889 :
    (3889 : ℕ).Prime ∧ logScale (3889 : ℚ) = 11 ∧
      (82659073312 : ℤ) = ⌊logCenter (3889 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3889 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3889 : Reach 3889 38200917808215 147536709517 := by
  have hr := row_3889
  have hl := log_bounds hr.1
    (by change logScale (3889 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3881) (T := 38118258734903) (U := 147498772589)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3881

theorem row_3907 :
    (3907 : ℕ).Prime ∧ logScale (3907 : ℚ) = 11 ∧
      (82705250921 : ℤ) = ⌊logCenter (3907 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3907 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3907 : Reach 3907 38283623059136 147574481333 := by
  have hr := row_3907
  have hl := log_bounds hr.1
    (by change logScale (3907 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3889) (T := 38200917808215) (U := 147536709517)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3889

#print axioms reach_3907

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
