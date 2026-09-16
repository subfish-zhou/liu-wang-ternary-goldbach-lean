import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0171

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4651 :
    (4651 : ℕ).Prime ∧ logScale (4651 : ℚ) = 12 ∧
      (84448375261 : ℤ) = ⌊logCenter (4651 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4651 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4651 : Reach 4651 45723461773337 150687264416 := by
  have hr := row_4651
  have hl := log_bounds hr.1
    (by change logScale (4651 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4649) (T := 45639013398076) (U := 150654865520)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4649

theorem row_4657 :
    (4657 : ℕ).Prime ∧ logScale (4657 : ℚ) = 12 ∧
      (84461267398 : ℤ) = ⌊logCenter (4657 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4657 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4657 : Reach 4657 45807923040735 150719628520 := by
  have hr := row_4657
  have hl := log_bounds hr.1
    (by change logScale (4657 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4651) (T := 45723461773337) (U := 150687264416)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4651

theorem row_4663 :
    (4663 : ℕ).Prime ∧ logScale (4663 : ℚ) = 12 ∧
      (84474142936 : ℤ) = ⌊logCenter (4663 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4663 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4663 : Reach 4663 45892397183671 150751957913 := by
  have hr := row_4663
  have hl := log_bounds hr.1
    (by change logScale (4663 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4657) (T := 45807923040735) (U := 150719628520)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4657

theorem row_4673 :
    (4673 : ℕ).Prime ∧ logScale (4673 : ℚ) = 12 ∧
      (84495565395 : ℤ) = ⌊logCenter (4673 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4673 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4673 : Reach 4673 45976892749066 150784225028 := by
  have hr := row_4673
  have hl := log_bounds hr.1
    (by change logScale (4673 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4663) (T := 45892397183671) (U := 150751957913)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4663

theorem row_4679 :
    (4679 : ℕ).Prime ∧ logScale (4679 : ℚ) = 12 ∧
      (84508396877 : ℤ) = ⌊logCenter (4679 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4679 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4679 : Reach 4679 46061401145943 150816457655 := by
  have hr := row_4679
  have hl := log_bounds hr.1
    (by change logScale (4679 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4673) (T := 45976892749066) (U := 150784225028)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4673

theorem row_4691 :
    (4691 : ℕ).Prime ∧ logScale (4691 : ℚ) = 12 ∧
      (84534010552 : ℤ) = ⌊logCenter (4691 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4691 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4691 : Reach 4691 46145935156495 150848614683 := by
  have hr := row_4691
  have hl := log_bounds hr.1
    (by change logScale (4691 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4679) (T := 46061401145943) (U := 150816457655)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4679

theorem row_4703 :
    (4703 : ℕ).Prime ∧ logScale (4703 : ℚ) = 12 ∧
      (84559558788 : ℤ) = ⌊logCenter (4703 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4703 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4703 : Reach 4703 46230494715283 150880696482 := by
  have hr := row_4703
  have hl := log_bounds hr.1
    (by change logScale (4703 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4691) (T := 46145935156495) (U := 150848614683)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4691

theorem row_4721 :
    (4721 : ℕ).Prime ∧ logScale (4721 : ℚ) = 12 ∧
      (84597759174 : ℤ) = ⌊logCenter (4721 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4721 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4721 : Reach 4721 46315092474457 150912662732 := by
  have hr := row_4721
  have hl := log_bounds hr.1
    (by change logScale (4721 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4703) (T := 46230494715283) (U := 150880696482)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4703

#print axioms reach_4721

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
