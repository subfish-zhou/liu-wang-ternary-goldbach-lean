import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block012

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3701 :
    (3701 : ℕ).Prime ∧ logScale (3701 : ℚ) = 11 ∧
      (82163583295 : ℤ) = ⌊logCenter (3701 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3701 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3701 : Reach 3701 36387444972944 146685073205 := by
  have hr := row_3701
  have hl := log_bounds hr.1
    (by change logScale (3701 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3697) (T := 36305281389649) (U := 146645439302)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3697

theorem row_3709 :
    (3709 : ℕ).Prime ∧ logScale (3709 : ℚ) = 11 ∧
      (82185175746 : ℤ) = ⌊logCenter (3709 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3709 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3709 : Reach 3709 36469630148690 146724632287 := by
  have hr := row_3709
  have hl := log_bounds hr.1
    (by change logScale (3709 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3701) (T := 36387444972944) (U := 146685073205)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3701

theorem row_3719 :
    (3719 : ℕ).Prime ∧ logScale (3719 : ℚ) = 11 ∧
      (82212100910 : ℤ) = ⌊logCenter (3719 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3719 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3719 : Reach 3719 36551842249600 146764095610 := by
  have hr := row_3719
  have hl := log_bounds hr.1
    (by change logScale (3719 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3709) (T := 36469630148690) (U := 146724632287)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3709

theorem row_3727 :
    (3727 : ℕ).Prime ∧ logScale (3727 : ℚ) = 11 ∧
      (82233588966 : ℤ) = ⌊logCenter (3727 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3727 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3727 : Reach 3727 36634075838566 146803484793 := by
  have hr := row_3727
  have hl := log_bounds hr.1
    (by change logScale (3727 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3719) (T := 36551842249600) (U := 146764095610)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3719

theorem row_3733 :
    (3733 : ℕ).Prime ∧ logScale (3733 : ℚ) = 11 ∧
      (82249674760 : ℤ) = ⌊logCenter (3733 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3733 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3733 : Reach 3733 36716325513326 146842821204 := by
  have hr := row_3733
  have hl := log_bounds hr.1
    (by change logScale (3733 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3727) (T := 36634075838566) (U := 146803484793)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3727

theorem row_3739 :
    (3739 : ℕ).Prime ∧ logScale (3739 : ℚ) = 11 ∧
      (82265734721 : ℤ) = ⌊logCenter (3739 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3739 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3739 : Reach 3739 36798591248047 146882104998 := by
  have hr := row_3739
  have hl := log_bounds hr.1
    (by change logScale (3739 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3733) (T := 36716325513326) (U := 146842821204)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3733

theorem row_3761 :
    (3761 : ℕ).Prime ∧ logScale (3761 : ℚ) = 11 ∧
      (82324401556 : ℤ) = ⌊logCenter (3761 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3761 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3761 : Reach 3761 36880915649603 146921169388 := by
  have hr := row_3761
  have hl := log_bounds hr.1
    (by change logScale (3761 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3739) (T := 36798591248047) (U := 146882104998)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3739

theorem row_3767 :
    (3767 : ℕ).Prime ∧ logScale (3767 : ℚ) = 11 ∧
      (82340342048 : ℤ) = ⌊logCenter (3767 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3767 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3767 : Reach 3767 36963255991651 146960181914 := by
  have hr := row_3767
  have hl := log_bounds hr.1
    (by change logScale (3767 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3761) (T := 36880915649603) (U := 146921169388)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3761

#print axioms reach_3767

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
