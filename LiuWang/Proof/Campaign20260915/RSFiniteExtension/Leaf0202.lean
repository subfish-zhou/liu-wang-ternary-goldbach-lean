import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0201

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5281 :
    (5281 : ℕ).Prime ∧ logScale (5281 : ℚ) = 12 ∧
      (85718707495 : ℤ) = ⌊logCenter (5281 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5281 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5281 : Reach 5281 51851157230873 152888891657 := by
  have hr := row_5281
  have hl := log_bounds hr.1
    (by change logScale (5281 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5279) (T := 51765438523378) (U := 152859940910)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5279

theorem row_5297 :
    (5297 : ℕ).Prime ∧ logScale (5297 : ℚ) = 12 ∧
      (85748958984 : ℤ) = ⌊logCenter (5297 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5297 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5297 : Reach 5297 51936906189857 152917760406 := by
  have hr := row_5297
  have hl := log_bounds hr.1
    (by change logScale (5297 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5281) (T := 51851157230873) (U := 152888891657)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5281

theorem row_5303 :
    (5303 : ℕ).Prime ∧ logScale (5303 : ℚ) = 12 ∧
      (85760279740 : ℤ) = ⌊logCenter (5303 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5303 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5303 : Reach 5303 52022666469597 152946601931 := by
  have hr := row_5303
  have hl := log_bounds hr.1
    (by change logScale (5303 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5297) (T := 51936906189857) (U := 152917760406)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5297

theorem row_5309 :
    (5309 : ℕ).Prime ∧ logScale (5309 : ℚ) = 12 ∧
      (85771587694 : ℤ) = ⌊logCenter (5309 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5309 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5309 : Reach 5309 52108438057291 152975416288 := by
  have hr := row_5309
  have hl := log_bounds hr.1
    (by change logScale (5309 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5303) (T := 52022666469597) (U := 152946601931)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5303

theorem row_5323 :
    (5323 : ℕ).Prime ∧ logScale (5323 : ℚ) = 12 ∧
      (85797923300 : ℤ) = ⌊logCenter (5323 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5323 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5323 : Reach 5323 52194235980591 153004160260 := by
  have hr := row_5323
  have hl := log_bounds hr.1
    (by change logScale (5323 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5309) (T := 52108438057291) (U := 152975416288)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5309

theorem row_5333 :
    (5333 : ℕ).Prime ∧ logScale (5333 : ℚ) = 12 ∧
      (85816692074 : ℤ) = ⌊logCenter (5333 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5333 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5333 : Reach 5333 52280052672665 153032855714 := by
  have hr := row_5333
  have hl := log_bounds hr.1
    (by change logScale (5333 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5323) (T := 52194235980591) (U := 153004160260)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5323

theorem row_5347 :
    (5347 : ℕ).Prime ∧ logScale (5347 : ℚ) = 12 ∧
      (85842909318 : ℤ) = ⌊logCenter (5347 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5347 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5347 : Reach 5347 52365895581983 153061481389 := by
  have hr := row_5347
  have hl := log_bounds hr.1
    (by change logScale (5347 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5333) (T := 52280052672665) (U := 153032855714)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5333

theorem row_5351 :
    (5351 : ℕ).Prime ∧ logScale (5351 : ℚ) = 12 ∧
      (85850387351 : ℤ) = ⌊logCenter (5351 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5351 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5351 : Reach 5351 52451745969334 153090091012 := by
  have hr := row_5351
  have hl := log_bounds hr.1
    (by change logScale (5351 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5347) (T := 52365895581983) (U := 153061481389)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5347

#print axioms reach_5351

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
