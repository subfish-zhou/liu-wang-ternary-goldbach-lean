import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0080

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2789 :
    (2789 : ℕ).Prime ∧ logScale (2789 : ℚ) = 11 ∧
      (79334383847 : ℤ) = ⌊logCenter (2789 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2789 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2789 : Reach 2789 27331696806172 141693748030 := by
  have hr := row_2789
  have hl := log_bounds hr.1
    (by change logScale (2789 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2777) (T := 27252362422325) (U := 141642943530)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2777

theorem row_2791 :
    (2791 : ℕ).Prime ∧ logScale (2791 : ℚ) = 11 ∧
      (79341552306 : ℤ) = ⌊logCenter (2791 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2791 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2791 : Reach 2791 27411038358478 141744534320 := by
  have hr := row_2791
  have hl := log_bounds hr.1
    (by change logScale (2791 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2789) (T := 27331696806172) (U := 141693748030)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2789

theorem row_2797 :
    (2797 : ℕ).Prime ∧ logScale (2797 : ℚ) = 11 ∧
      (79363026903 : ℤ) = ⌊logCenter (2797 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2797 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2797 : Reach 2797 27490401385381 141795229791 := by
  have hr := row_2797
  have hl := log_bounds hr.1
    (by change logScale (2797 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2791) (T := 27411038358478) (U := 141744534320)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2791

theorem row_2801 :
    (2801 : ℕ).Prime ∧ logScale (2801 : ℚ) = 11 ∧
      (79377317724 : ℤ) = ⌊logCenter (2801 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2801 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2801 : Reach 2801 27569778703105 141845870945 := by
  have hr := row_2801
  have hl := log_bounds hr.1
    (by change logScale (2801 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2797) (T := 27490401385381) (U := 141795229791)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2797

theorem row_2803 :
    (2803 : ℕ).Prime ∧ logScale (2803 : ℚ) = 11 ∧
      (79384455483 : ℤ) = ⌊logCenter (2803 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2803 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2803 : Reach 2803 27649163158588 141896494026 := by
  have hr := row_2803
  have hl := log_bounds hr.1
    (by change logScale (2803 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2801) (T := 27569778703105) (U := 141845870945)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2801

theorem row_2819 :
    (2819 : ℕ).Prime ∧ logScale (2819 : ℚ) = 11 ∧
      (79441374882 : ℤ) = ⌊logCenter (2819 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2819 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2819 : Reach 2819 27728604533470 141946847644 := by
  have hr := row_2819
  have hl := log_bounds hr.1
    (by change logScale (2819 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2803) (T := 27649163158588) (U := 141896494026)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2803

theorem row_2833 :
    (2833 : ℕ).Prime ∧ logScale (2833 : ℚ) = 11 ∧
      (79490914969 : ℤ) = ⌊logCenter (2833 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2833 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2833 : Reach 2833 27808095448439 141996970119 := by
  have hr := row_2833
  have hl := log_bounds hr.1
    (by change logScale (2833 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2819) (T := 27728604533470) (U := 141946847644)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2819

theorem row_2837 :
    (2837 : ℕ).Prime ∧ logScale (2837 : ℚ) = 11 ∧
      (79505024319 : ℤ) = ⌊logCenter (2837 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2837 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2837 : Reach 2837 27887600472758 142047039573 := by
  have hr := row_2837
  have hl := log_bounds hr.1
    (by change logScale (2837 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2833) (T := 27808095448439) (U := 141996970119)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2833

#print axioms reach_2837

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
