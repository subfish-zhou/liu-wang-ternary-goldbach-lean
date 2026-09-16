import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2719 :
    (2719 : ℕ).Prime ∧ logScale (2719 : ℚ) = 11 ∧
      (79080194417 : ℤ) = ⌊logCenter (2719 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2719 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2719 : Reach 2719 26698019660539 141282721898 := by
  have hr := row_2719
  have hl := log_bounds hr.1
    (by change logScale (2719 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2713) (T := 26618939466122) (U := 141230760617)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2713

theorem row_2729 :
    (2729 : ℕ).Prime ∧ logScale (2729 : ℚ) = 11 ∧
      (79116905178 : ℤ) = ⌊logCenter (2729 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2729 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2729 : Reach 2729 26777136565717 141334511753 := by
  have hr := row_2729
  have hl := log_bounds hr.1
    (by change logScale (2729 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2719) (T := 26698019660539) (U := 141282721898)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2719

theorem row_2731 :
    (2731 : ℕ).Prime ∧ logScale (2731 : ℚ) = 11 ∧
      (79124231186 : ℤ) = ⌊logCenter (2731 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2731 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2731 : Reach 2731 26856260796903 141386282637 := by
  have hr := row_2731
  have hl := log_bounds hr.1
    (by change logScale (2731 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2729) (T := 26777136565717) (U := 141334511753)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2729

theorem row_2741 :
    (2741 : ℕ).Prime ∧ logScale (2741 : ℚ) = 11 ∧
      (79160780934 : ℤ) = ⌊logCenter (2741 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2741 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2741 : Reach 2741 26935421577837 141437883471 := by
  have hr := row_2741
  have hl := log_bounds hr.1
    (by change logScale (2741 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2731) (T := 26856260796903) (U := 141386282637)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2731

theorem row_2749 :
    (2749 : ℕ).Prime ∧ logScale (2749 : ℚ) = 11 ∧
      (79189924853 : ℤ) = ⌊logCenter (2749 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2749 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2749 : Reach 2749 27014611502690 141489352861 := by
  have hr := row_2749
  have hl := log_bounds hr.1
    (by change logScale (2749 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2741) (T := 26935421577837) (U := 141437883471)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2741

theorem row_2753 :
    (2753 : ℕ).Prime ∧ logScale (2753 : ℚ) = 11 ∧
      (79204465022 : ℤ) = ⌊logCenter (2753 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2753 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2753 : Reach 2753 27093815967712 141540766144 := by
  have hr := row_2753
  have hl := log_bounds hr.1
    (by change logScale (2753 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2749) (T := 27014611502690) (U := 141489352861)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2749

theorem row_2767 :
    (2767 : ℕ).Prime ∧ logScale (2767 : ℚ) = 11 ∧
      (79255189769 : ℤ) = ⌊logCenter (2767 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2767 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2767 : Reach 2767 27173071157481 141591937788 := by
  have hr := row_2767
  have hl := log_bounds hr.1
    (by change logScale (2767 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2753) (T := 27093815967712) (U := 141540766144)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2753

theorem row_2777 :
    (2777 : ℕ).Prime ∧ logScale (2777 : ℚ) = 11 ∧
      (79291264844 : ℤ) = ⌊logCenter (2777 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2777 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2777 : Reach 2777 27252362422325 141642943530 := by
  have hr := row_2777
  have hl := log_bounds hr.1
    (by change logScale (2777 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2767) (T := 27173071157481) (U := 141591937788)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2767

#print axioms reach_2777

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
