import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0221

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5689 :
    (5689 : ℕ).Prime ∧ logScale (5689 : ℚ) = 12 ∧
      (86462897616 : ℤ) = ⌊logCenter (5689 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5689 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5689 : Reach 5689 55984771910269 154230531958 := by
  have hr := row_5689
  have hl := log_bounds hr.1
    (by change logScale (5689 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5683) (T := 55898309012653) (U := 154203421651)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5683

theorem row_5693 :
    (5693 : ℕ).Prime ∧ logScale (5693 : ℚ) = 12 ∧
      (86469926258 : ℤ) = ⌊logCenter (5693 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5693 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5693 : Reach 5693 56071241836527 154257627976 := by
  have hr := row_5693
  have hl := log_bounds hr.1
    (by change logScale (5693 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5689) (T := 55984771910269) (U := 154230531958)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5689

theorem row_5701 :
    (5701 : ℕ).Prime ∧ logScale (5701 : ℚ) = 12 ∧
      (86483968739 : ℤ) = ⌊logCenter (5701 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5701 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5701 : Reach 5701 56157725805266 154284690718 := by
  have hr := row_5701
  have hl := log_bounds hr.1
    (by change logScale (5701 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5693) (T := 56071241836527) (U := 154257627976)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5693

theorem row_5711 :
    (5711 : ℕ).Prime ∧ logScale (5711 : ℚ) = 12 ∧
      (86501494155 : ℤ) = ⌊logCenter (5711 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5711 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5711 : Reach 5711 56244227299421 154311710804 := by
  have hr := row_5711
  have hl := log_bounds hr.1
    (by change logScale (5711 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5701) (T := 56157725805266) (U := 154284690718)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5701

theorem row_5717 :
    (5717 : ℕ).Prime ∧ logScale (5717 : ℚ) = 12 ∧
      (86511994681 : ℤ) = ⌊logCenter (5717 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5717 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5717 : Reach 5717 56330739294102 154338707255 := by
  have hr := row_5717
  have hl := log_bounds hr.1
    (by change logScale (5717 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5711) (T := 56244227299421) (U := 154311710804)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5711

theorem row_5737 :
    (5737 : ℕ).Prime ∧ logScale (5737 : ℚ) = 12 ∧
      (86546917014 : ℤ) = ⌊logCenter (5737 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5737 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5737 : Reach 5737 56417286211116 154365614283 := by
  have hr := row_5737
  have hl := log_bounds hr.1
    (by change logScale (5737 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5717) (T := 56330739294102) (U := 154338707255)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5717

theorem row_5741 :
    (5741 : ℕ).Prime ∧ logScale (5741 : ℚ) = 12 ∧
      (86553886870 : ℤ) = ⌊logCenter (5741 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5741 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5741 : Reach 5741 56503840097986 154392507248 := by
  have hr := row_5741
  have hl := log_bounds hr.1
    (by change logScale (5741 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5737) (T := 56417286211116) (U := 154365614283)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5737

theorem row_5743 :
    (5743 : ℕ).Prime ∧ logScale (5743 : ℚ) = 12 ∧
      (86557369977 : ℤ) = ⌊logCenter (5743 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5743 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5743 : Reach 5743 56590397467963 154419395529 := by
  have hr := row_5743
  have hl := log_bounds hr.1
    (by change logScale (5743 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5741) (T := 56503840097986) (U := 154392507248)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5741

#print axioms reach_5743

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
