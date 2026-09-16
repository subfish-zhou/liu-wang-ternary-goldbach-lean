import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0140

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3967 :
    (3967 : ℕ).Prime ∧ logScale (3967 : ℚ) = 11 ∧
      (82857654176 : ℤ) = ⌊logCenter (3967 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3967 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3967 : Reach 3967 39028541023153 147912711826 := by
  have hr := row_3967
  have hl := log_bounds hr.1
    (by change logScale (3967 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3947) (T := 38945683368977) (U := 147875426040)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3947

theorem row_3989 :
    (3989 : ℕ).Prime ∧ logScale (3989 : ℚ) = 11 ∧
      (82912958490 : ℤ) = ⌊logCenter (3989 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3989 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3989 : Reach 3989 39111453981643 147949801273 := by
  have hr := row_3989
  have hl := log_bounds hr.1
    (by change logScale (3989 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3967) (T := 39028541023153) (U := 147912711826)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3967

theorem row_4001 :
    (4001 : ℕ).Prime ∧ logScale (4001 : ℚ) = 11 ∧
      (82942996059 : ℤ) = ⌊logCenter (4001 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4001 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4001 : Reach 4001 39194396977702 147986788724 := by
  have hr := row_4001
  have hl := log_bounds hr.1
    (by change logScale (4001 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3989) (T := 39111453981643) (U := 147949801273)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3989

theorem row_4003 :
    (4003 : ℕ).Prime ∧ logScale (4003 : ℚ) = 11 ∧
      (82947993561 : ℤ) = ⌊logCenter (4003 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4003 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4003 : Reach 4003 39277344971263 148023766933 := by
  have hr := row_4003
  have hl := log_bounds hr.1
    (by change logScale (4003 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4001) (T := 39194396977702) (U := 147986788724)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4001

theorem row_4007 :
    (4007 : ℕ).Prime ∧ logScale (4007 : ℚ) = 11 ∧
      (82957981077 : ℤ) = ⌊logCenter (4007 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4007 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4007 : Reach 4007 39360302952340 148060717449 := by
  have hr := row_4007
  have hl := log_bounds hr.1
    (by change logScale (4007 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4003) (T := 39277344971263) (U := 148023766933)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4003

theorem row_4013 :
    (4013 : ℕ).Prime ∧ logScale (4013 : ℚ) = 11 ∧
      (82972943674 : ℤ) = ⌊logCenter (4013 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4013 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4013 : Reach 4013 39443275896014 148097621915 := by
  have hr := row_4013
  have hl := log_bounds hr.1
    (by change logScale (4013 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4007) (T := 39360302952340) (U := 148060717449)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4007

theorem row_4019 :
    (4019 : ℕ).Prime ∧ logScale (4019 : ℚ) = 11 ∧
      (82987883915 : ℤ) = ⌊logCenter (4019 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4019 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4019 : Reach 4019 39526263779929 148134480458 := by
  have hr := row_4019
  have hl := log_bounds hr.1
    (by change logScale (4019 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4013) (T := 39443275896014) (U := 148097621915)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4013

theorem row_4021 :
    (4021 : ℕ).Prime ∧ logScale (4021 : ℚ) = 11 ∧
      (82992859040 : ℤ) = ⌊logCenter (4021 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4021 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4021 : Reach 4021 39609256638969 148171329832 := by
  have hr := row_4021
  have hl := log_bounds hr.1
    (by change logScale (4021 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4019) (T := 39526263779929) (U := 148134480458)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4019

#print axioms reach_4021

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
