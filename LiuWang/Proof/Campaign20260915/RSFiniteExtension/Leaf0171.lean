import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0170

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4591 :
    (4591 : ℕ).Prime ∧ logScale (4591 : ℚ) = 12 ∧
      (84318531411 : ℤ) = ⌊logCenter (4591 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4591 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4591 : Reach 4591 45048237502805 150427089824 := by
  have hr := row_4591
  have hl := log_bounds hr.1
    (by change logScale (4591 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4583) (T := 44963918971394) (U := 150394324176)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4583

theorem row_4597 :
    (4597 : ℕ).Prime ∧ logScale (4597 : ℚ) = 12 ∧
      (84331591926 : ℤ) = ⌊logCenter (4597 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4597 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4597 : Reach 4597 45132569094731 150459819827 := by
  have hr := row_4597
  have hl := log_bounds hr.1
    (by change logScale (4597 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4591) (T := 45048237502805) (U := 150427089824)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4591

theorem row_4603 :
    (4603 : ℕ).Prime ∧ logScale (4603 : ℚ) = 12 ∧
      (84344635406 : ℤ) = ⌊logCenter (4603 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4603 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4603 : Reach 4603 45216913730137 150492514269 := by
  have hr := row_4603
  have hl := log_bounds hr.1
    (by change logScale (4603 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4597) (T := 45132569094731) (U := 150459819827)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4597

theorem row_4621 :
    (4621 : ℕ).Prime ∧ logScale (4621 : ℚ) = 12 ∧
      (84383664077 : ℤ) = ⌊logCenter (4621 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4621 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4621 : Reach 4621 45301297394214 150525088407 := by
  have hr := row_4621
  have hl := log_bounds hr.1
    (by change logScale (4621 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4603) (T := 45216913730137) (U := 150492514269)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4603

theorem row_4637 :
    (4637 : ℕ).Prime ∧ logScale (4637 : ℚ) = 12 ∧
      (84418228812 : ℤ) = ⌊logCenter (4637 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4637 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4637 : Reach 4637 45385715623026 150557557150 := by
  have hr := row_4637
  have hl := log_bounds hr.1
    (by change logScale (4637 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4621) (T := 45301297394214) (U := 150525088407)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4621

theorem row_4639 :
    (4639 : ℕ).Prime ∧ logScale (4639 : ℚ) = 12 ∧
      (84422541016 : ℤ) = ⌊logCenter (4639 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4639 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4639 : Reach 4639 45470138164042 150590018892 := by
  have hr := row_4639
  have hl := log_bounds hr.1
    (by change logScale (4639 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4637) (T := 45385715623026) (U := 150557557150)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4637

theorem row_4643 :
    (4643 : ℕ).Prime ∧ logScale (4643 : ℚ) = 12 ∧
      (84431159849 : ℤ) = ⌊logCenter (4643 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4643 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4643 : Reach 4643 45554569323891 150622459655 := by
  have hr := row_4643
  have hl := log_bounds hr.1
    (by change logScale (4643 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4639) (T := 45470138164042) (U := 150590018892)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4639

theorem row_4649 :
    (4649 : ℕ).Prime ∧ logScale (4649 : ℚ) = 12 ∧
      (84444074185 : ℤ) = ⌊logCenter (4649 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4649 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4649 : Reach 4649 45639013398076 150654865520 := by
  have hr := row_4649
  have hl := log_bounds hr.1
    (by change logScale (4649 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4643) (T := 45554569323891) (U := 150622459655)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4643

#print axioms reach_4649

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
