import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0130

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3769 :
    (3769 : ℕ).Prime ∧ logScale (3769 : ℚ) = 11 ∧
      (82345649904 : ℤ) = ⌊logCenter (3769 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3769 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3769 : Reach 3769 37045601641555 146999184086 := by
  have hr := row_3769
  have hl := log_bounds hr.1
    (by change logScale (3769 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3767) (T := 36963255991651) (U := 146960181914)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3767

theorem row_3779 :
    (3779 : ℕ).Prime ∧ logScale (3779 : ℚ) = 11 ∧
      (82372147004 : ℤ) = ⌊logCenter (3779 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3779 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3779 : Reach 3779 37127973788559 147038093346 := by
  have hr := row_3779
  have hl := log_bounds hr.1
    (by change logScale (3779 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3769) (T := 37045601641555) (U := 146999184086)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3769

theorem row_3793 :
    (3793 : ℕ).Prime ∧ logScale (3793 : ℚ) = 11 ∧
      (82409125388 : ℤ) = ⌊logCenter (3793 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3793 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3793 : Reach 3793 37210382913947 147076869215 := by
  have hr := row_3793
  have hl := log_bounds hr.1
    (by change logScale (3793 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3779) (T := 37127973788559) (U := 147038093346)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3779

theorem row_3797 :
    (3797 : ℕ).Prime ∧ logScale (3797 : ℚ) = 11 ∧
      (82419665573 : ℤ) = ⌊logCenter (3797 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3797 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3797 : Reach 3797 37292802579520 147115614439 := by
  have hr := row_3797
  have hl := log_bounds hr.1
    (by change logScale (3797 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3793) (T := 37210382913947) (U := 147076869215)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3793

theorem row_3803 :
    (3803 : ℕ).Prime ∧ logScale (3803 : ℚ) = 11 ∧
      (82435455050 : ℤ) = ⌊logCenter (3803 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3803 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3803 : Reach 3803 37375238034570 147154308709 := by
  have hr := row_3803
  have hl := log_bounds hr.1
    (by change logScale (3803 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3797) (T := 37292802579520) (U := 147115614439)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3797

theorem row_3821 :
    (3821 : ℕ).Prime ∧ logScale (3821 : ℚ) = 11 ∧
      (82482674445 : ℤ) = ⌊logCenter (3821 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3821 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3821 : Reach 3821 37457720709015 147192830780 := by
  have hr := row_3821
  have hl := log_bounds hr.1
    (by change logScale (3821 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3803) (T := 37375238034570) (U := 147154308709)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3803

theorem row_3823 :
    (3823 : ℕ).Prime ∧ logScale (3823 : ℚ) = 11 ∧
      (82487907308 : ℤ) = ⌊logCenter (3823 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3823 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3823 : Reach 3823 37540208616323 147231342772 := by
  have hr := row_3823
  have hl := log_bounds hr.1
    (by change logScale (3823 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3821) (T := 37457720709015) (U := 147192830780)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3821

theorem row_3833 :
    (3833 : ℕ).Prime ∧ logScale (3833 : ℚ) = 11 ∧
      (82514030625 : ℤ) = ⌊logCenter (3833 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3833 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3833 : Reach 3833 37622722646948 147269764313 := by
  have hr := row_3833
  have hl := log_bounds hr.1
    (by change logScale (3833 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3823) (T := 37540208616323) (U := 147231342772)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3823

#print axioms reach_3833

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
