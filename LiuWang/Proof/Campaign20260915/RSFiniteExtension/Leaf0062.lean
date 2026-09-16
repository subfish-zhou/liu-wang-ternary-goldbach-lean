import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0061

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2467 :
    (2467 : ℕ).Prime ∧ logScale (2467 : ℚ) = 11 ∧
      (78107581136 : ℤ) = ⌊logCenter (2467 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2467 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2467 : Reach 2467 24179747614043 139564346320 := by
  have hr := row_2467
  have hl := log_bounds hr.1
    (by change logScale (2467 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2459) (T := 24101640032907) (U := 139507773824)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2459

theorem row_2473 :
    (2473 : ℕ).Prime ∧ logScale (2473 : ℚ) = 11 ∧
      (78131872646 : ℤ) = ⌊logCenter (2473 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2473 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2473 : Reach 2473 24257879486689 139620804389 := by
  have hr := row_2473
  have hl := log_bounds hr.1
    (by change logScale (2473 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2467) (T := 24179747614043) (U := 139564346320)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2467

theorem row_2477 :
    (2477 : ℕ).Prime ∧ logScale (2477 : ℚ) = 11 ∧
      (78148034266 : ℤ) = ⌊logCenter (2477 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2477 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2477 : Reach 2477 24336027520955 139677194052 := by
  have hr := row_2477
  have hl := log_bounds hr.1
    (by change logScale (2477 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2473) (T := 24257879486689) (U := 139620804389)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2473

theorem row_2503 :
    (2503 : ℕ).Prime ∧ logScale (2503 : ℚ) = 11 ∧
      (78252452885 : ℤ) = ⌊logCenter (2503 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2503 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2503 : Reach 2503 24414279973840 139733020269 := by
  have hr := row_2503
  have hl := log_bounds hr.1
    (by change logScale (2503 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2477) (T := 24336027520955) (U := 139677194052)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2477

theorem row_2521 :
    (2521 : ℕ).Prime ∧ logScale (2521 : ℚ) = 11 ∧
      (78324109243 : ℤ) = ⌊logCenter (2521 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2521 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2521 : Reach 2521 24492604083083 139788469881 := by
  have hr := row_2521
  have hl := log_bounds hr.1
    (by change logScale (2521 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2503) (T := 24414279973840) (U := 139733020269)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2503

theorem row_2531 :
    (2531 : ℕ).Prime ∧ logScale (2531 : ℚ) = 11 ∧
      (78363697576 : ℤ) = ⌊logCenter (2531 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2531 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2531 : Reach 2531 24570967780659 139843722241 := by
  have hr := row_2531
  have hl := log_bounds hr.1
    (by change logScale (2531 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2521) (T := 24492604083083) (U := 139788469881)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2521

theorem row_2539 :
    (2539 : ℕ).Prime ∧ logScale (2539 : ℚ) = 11 ∧
      (78395255788 : ℤ) = ⌊logCenter (2539 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2539 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2539 : Reach 2539 24649363036447 139898822211 := by
  have hr := row_2539
  have hl := log_bounds hr.1
    (by change logScale (2539 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2531) (T := 24570967780659) (U := 139843722241)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2531

theorem row_2543 :
    (2543 : ℕ).Prime ∧ logScale (2543 : ℚ) = 11 ∧
      (78410997625 : ℤ) = ⌊logCenter (2543 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2543 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2543 : Reach 2543 24727774034072 139953857153 := by
  have hr := row_2543
  have hl := log_bounds hr.1
    (by change logScale (2543 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2539) (T := 24649363036447) (U := 139898822211)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2539

#print axioms reach_2543

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
