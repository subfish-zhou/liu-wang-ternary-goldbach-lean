import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0101

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3259 :
    (3259 : ℕ).Prime ∧ logScale (3259 : ℚ) = 11 ∧
      (80891756759 : ℤ) = ⌊logCenter (3259 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3259 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3259 : Reach 3259 31819163785987 144348308779 := by
  have hr := row_3259
  have hl := log_bounds hr.1
    (by change logScale (3259 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3257) (T := 31738272029228) (U := 144304016570)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3257

theorem row_3271 :
    (3271 : ℕ).Prime ∧ logScale (3271 : ℚ) = 11 ∧
      (80928510246 : ℤ) = ⌊logCenter (3271 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3271 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3271 : Reach 3271 31900092296233 144392451993 := by
  have hr := row_3271
  have hl := log_bounds hr.1
    (by change logScale (3271 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3259) (T := 31819163785987) (U := 144348308779)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3259

theorem row_3299 :
    (3299 : ℕ).Prime ∧ logScale (3299 : ℚ) = 11 ∧
      (81013746683 : ℤ) = ⌊logCenter (3299 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3299 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3299 : Reach 3299 31981106042916 144436233816 := by
  have hr := row_3299
  have hl := log_bounds hr.1
    (by change logScale (3299 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3271) (T := 31900092296233) (U := 144392451993)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3271

theorem row_3301 :
    (3301 : ℕ).Prime ∧ logScale (3301 : ℚ) = 11 ∧
      (81019807289 : ℤ) = ⌊logCenter (3301 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3301 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3301 : Reach 3301 32062125850205 144480002372 := by
  have hr := row_3301
  have hl := log_bounds hr.1
    (by change logScale (3301 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3299) (T := 31981106042916) (U := 144436233816)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3299

theorem row_3307 :
    (3307 : ℕ).Prime ∧ logScale (3307 : ℚ) = 11 ∧
      (81037967101 : ℤ) = ⌊logCenter (3307 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3307 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3307 : Reach 3307 32143163817306 144523704733 := by
  have hr := row_3307
  have hl := log_bounds hr.1
    (by change logScale (3307 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3301) (T := 32062125850205) (U := 144480002372)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3301

theorem row_3313 :
    (3313 : ℕ).Prime ∧ logScale (3313 : ℚ) = 11 ∧
      (81056093994 : ℤ) = ⌊logCenter (3313 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3313 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3313 : Reach 3313 32224219911300 144567341118 := by
  have hr := row_3313
  have hl := log_bounds hr.1
    (by change logScale (3313 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3307) (T := 32143163817306) (U := 144523704733)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3307

theorem row_3319 :
    (3319 : ℕ).Prime ∧ logScale (3319 : ℚ) = 11 ∧
      (81074188088 : ℤ) = ⌊logCenter (3319 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3319 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3319 : Reach 3319 32305294099388 144610911746 := by
  have hr := row_3319
  have hl := log_bounds hr.1
    (by change logScale (3319 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3313) (T := 32224219911300) (U := 144567341118)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3313

theorem row_3323 :
    (3323 : ℕ).Prime ∧ logScale (3323 : ℚ) = 11 ∧
      (81086232654 : ℤ) = ⌊logCenter (3323 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3323 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3323 : Reach 3323 32386380332042 144654443026 := by
  have hr := row_3323
  have hl := log_bounds hr.1
    (by change logScale (3323 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3319) (T := 32305294099388) (U := 144610911746)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3319

#print axioms reach_3323

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
