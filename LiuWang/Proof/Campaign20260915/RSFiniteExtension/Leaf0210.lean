import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block020

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5381 :
    (5381 : ℕ).Prime ∧ logScale (5381 : ℚ) = 12 ∧
      (85906295063 : ℤ) = ⌊logCenter (5381 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5381 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5381 : Reach 5381 52537652264397 153118546420 := by
  have hr := row_5381
  have hl := log_bounds hr.1
    (by change logScale (5381 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5351) (T := 52451745969334) (U := 153090091012)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5351

theorem row_5387 :
    (5387 : ℕ).Prime ∧ logScale (5387 : ℚ) = 12 ∧
      (85917439195 : ℤ) = ⌊logCenter (5387 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5387 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5387 : Reach 5387 52623569703592 153146975412 := by
  have hr := row_5387
  have hl := log_bounds hr.1
    (by change logScale (5387 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5381) (T := 52537652264397) (U := 153118546420)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5381

theorem row_5393 :
    (5393 : ℕ).Prime ∧ logScale (5393 : ℚ) = 12 ∧
      (85928570922 : ℤ) = ⌊logCenter (5393 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5393 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5393 : Reach 5393 52709498274514 153175378041 := by
  have hr := row_5393
  have hl := log_bounds hr.1
    (by change logScale (5393 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5387) (T := 52623569703592) (U := 153146975412)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5387

theorem row_5399 :
    (5399 : ℕ).Prime ∧ logScale (5399 : ℚ) = 12 ∧
      (85939690270 : ℤ) = ⌊logCenter (5399 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5399 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5399 : Reach 5399 52795437964784 153203754362 := by
  have hr := row_5399
  have hl := log_bounds hr.1
    (by change logScale (5399 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5393) (T := 52709498274514) (U := 153175378041)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5393

theorem row_5407 :
    (5407 : ℕ).Prime ∧ logScale (5407 : ℚ) = 12 ∧
      (85954496862 : ℤ) = ⌊logCenter (5407 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5407 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5407 : Reach 5407 52881392461646 153232093940 := by
  have hr := row_5407
  have hl := log_bounds hr.1
    (by change logScale (5407 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5399) (T := 52795437964784) (U := 153203754362)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5399

theorem row_5413 :
    (5413 : ℕ).Prime ∧ logScale (5413 : ℚ) = 12 ∧
      (85965587436 : ℤ) = ⌊logCenter (5413 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5413 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5413 : Reach 5413 52967358049082 153260407336 := by
  have hr := row_5413
  have hl := log_bounds hr.1
    (by change logScale (5413 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5407) (T := 52881392461646) (U := 153232093940)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5407

theorem row_5417 :
    (5417 : ℕ).Prime ∧ logScale (5417 : ℚ) = 12 ∧
      (85972974325 : ℤ) = ⌊logCenter (5417 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5417 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5417 : Reach 5417 53053331023407 153288705048 := by
  have hr := row_5417
  have hl := log_bounds hr.1
    (by change logScale (5417 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5413) (T := 52967358049082) (U := 153260407336)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5413

theorem row_5419 :
    (5419 : ℕ).Prime ∧ logScale (5419 : ℚ) = 12 ∧
      (85976665724 : ℤ) = ⌊logCenter (5419 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5419 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5419 : Reach 5419 53139307689131 153316997537 := by
  have hr := row_5419
  have hl := log_bounds hr.1
    (by change logScale (5419 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5417) (T := 53053331023407) (U := 153288705048)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5417

#print axioms reach_5419

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
