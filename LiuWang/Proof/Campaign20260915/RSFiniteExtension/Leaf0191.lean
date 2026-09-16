import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0190

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4999 :
    (4999 : ℕ).Prime ∧ logScale (4999 : ℚ) = 12 ∧
      (85169931682 : ℤ) = ⌊logCenter (4999 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4999 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4999 : Reach 4999 49116953499162 151939385514 := by
  have hr := row_4999
  have hl := log_bounds hr.1
    (by change logScale (4999 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4993) (T := 49031783567480) (U := 151908991558)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4993

theorem row_5003 :
    (5003 : ℕ).Prime ∧ logScale (5003 : ℚ) = 12 ∧
      (85177930083 : ℤ) = ⌊logCenter (5003 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5003 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5003 : Reach 5003 49202131429245 151969761241 := by
  have hr := row_5003
  have hl := log_bounds hr.1
    (by change logScale (5003 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4999) (T := 49116953499162) (U := 151939385514)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4999

theorem row_5009 :
    (5009 : ℕ).Prime ∧ logScale (5009 : ℚ) = 12 ∧
      (85189915702 : ℤ) = ⌊logCenter (5009 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5009 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5009 : Reach 5009 49287321344947 152000106641 := by
  have hr := row_5009
  have hl := log_bounds hr.1
    (by change logScale (5009 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5003) (T := 49202131429245) (U := 151969761241)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5003

theorem row_5011 :
    (5011 : ℕ).Prime ∧ logScale (5011 : ℚ) = 12 ∧
      (85193907718 : ℤ) = ⌊logCenter (5011 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5011 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5011 : Reach 5011 49372515252665 152030445984 := by
  have hr := row_5011
  have hl := log_bounds hr.1
    (by change logScale (5011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5009) (T := 49287321344947) (U := 152000106641)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5009

theorem row_5021 :
    (5021 : ℕ).Prime ∧ logScale (5021 : ℚ) = 12 ∧
      (85213843929 : ℤ) = ⌊logCenter (5021 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5021 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5021 : Reach 5021 49457729096594 152060730934 := by
  have hr := row_5021
  have hl := log_bounds hr.1
    (by change logScale (5021 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5011) (T := 49372515252665) (U := 152030445984)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5011

theorem row_5023 :
    (5023 : ℕ).Prime ∧ logScale (5023 : ℚ) = 12 ∧
      (85217826406 : ℤ) = ⌊logCenter (5023 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5023 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5023 : Reach 5023 49542946923000 152091009853 := by
  have hr := row_5023
  have hl := log_bounds hr.1
    (by change logScale (5023 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5021) (T := 49457729096594) (U := 152060730934)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5021

theorem row_5039 :
    (5039 : ℕ).Prime ∧ logScale (5039 : ℚ) = 12 ∧
      (85249629255 : ℤ) = ⌊logCenter (5039 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5039 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5039 : Reach 5039 49628196552255 152121198621 := by
  have hr := row_5039
  have hl := log_bounds hr.1
    (by change logScale (5039 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5023) (T := 49542946923000) (U := 152091009853)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5023

theorem row_5051 :
    (5051 : ℕ).Prime ∧ logScale (5051 : ℚ) = 12 ∧
      (85273415193 : ℤ) = ⌊logCenter (5051 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5051 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5051 : Reach 5051 49713469967448 152151321631 := by
  have hr := row_5051
  have hl := log_bounds hr.1
    (by change logScale (5051 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5039) (T := 49628196552255) (U := 152121198621)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5039

#print axioms reach_5051

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
