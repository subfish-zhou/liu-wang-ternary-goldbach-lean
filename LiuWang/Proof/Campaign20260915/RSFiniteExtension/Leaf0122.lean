import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0121

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3637 :
    (3637 : ℕ).Prime ∧ logScale (3637 : ℚ) = 11 ∧
      (81989144421 : ℤ) = ⌊logCenter (3637 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3637 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3637 : Reach 3637 35730668654507 146366184755 := by
  have hr := row_3637
  have hl := log_bounds hr.1
    (by change logScale (3637 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3631) (T := 35648679510086) (U := 146325941096)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3631

theorem row_3643 :
    (3643 : ℕ).Prime ∧ logScale (3643 : ℚ) = 11 ∧
      (82005627941 : ℤ) = ⌊logCenter (3643 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3643 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3643 : Reach 3643 35812674282448 146406373164 := by
  have hr := row_3643
  have hl := log_bounds hr.1
    (by change logScale (3643 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3637) (T := 35730668654507) (U := 146366184755)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3637

theorem row_3659 :
    (3659 : ℕ).Prime ∧ logScale (3659 : ℚ) = 11 ∧
      (82049451621 : ℤ) = ⌊logCenter (3659 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3659 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3659 : Reach 3659 35894723734069 146446396777 := by
  have hr := row_3659
  have hl := log_bounds hr.1
    (by change logScale (3659 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3643) (T := 35812674282448) (U := 146406373164)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3643

theorem row_3671 :
    (3671 : ℕ).Prime ∧ logScale (3671 : ℚ) = 11 ∧
      (82082193806 : ℤ) = ⌊logCenter (3671 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3671 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3671 : Reach 3671 35976805927875 146486300428 := by
  have hr := row_3671
  have hl := log_bounds hr.1
    (by change logScale (3671 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3659) (T := 35894723734069) (U := 146446396777)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3659

theorem row_3673 :
    (3673 : ℕ).Prime ∧ logScale (3673 : ℚ) = 11 ∧
      (82087640429 : ℤ) = ⌊logCenter (3673 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3673 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3673 : Reach 3673 36058893568304 146526193212 := by
  have hr := row_3673
  have hl := log_bounds hr.1
    (by change logScale (3673 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3671) (T := 35976805927875) (U := 146486300428)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3671

theorem row_3677 :
    (3677 : ℕ).Prime ∧ logScale (3677 : ℚ) = 11 ∧
      (82098524784 : ℤ) = ⌊logCenter (3677 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3677 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3677 : Reach 3677 36140992093088 146566053439 := by
  have hr := row_3677
  have hl := log_bounds hr.1
    (by change logScale (3677 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3673) (T := 36058893568304) (U := 146526193212)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3673

theorem row_3691 :
    (3691 : ℕ).Prime ∧ logScale (3691 : ℚ) = 11 ∧
      (82136527001 : ℤ) = ⌊logCenter (3691 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3691 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3691 : Reach 3691 36223128620089 146605773237 := by
  have hr := row_3691
  have hl := log_bounds hr.1
    (by change logScale (3691 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3677) (T := 36140992093088) (U := 146566053439)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3677

theorem row_3697 :
    (3697 : ℕ).Prime ∧ logScale (3697 : ℚ) = 11 ∧
      (82152769560 : ℤ) = ⌊logCenter (3697 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3697 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3697 : Reach 3697 36305281389649 146645439302 := by
  have hr := row_3697
  have hl := log_bounds hr.1
    (by change logScale (3697 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3691) (T := 36223128620089) (U := 146605773237)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3691

#print axioms reach_3697

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
