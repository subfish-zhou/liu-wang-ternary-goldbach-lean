import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0120

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3581 :
    (3581 : ℕ).Prime ∧ logScale (3581 : ℚ) = 11 ∧
      (81833973671 : ℤ) = ⌊logCenter (3581 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3581 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3581 : Reach 3581 35075286058183 146042403358 := by
  have hr := row_3581
  have hl := log_bounds hr.1
    (by change logScale (3581 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3571) (T := 34993452084512) (U := 146001620782)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3571

theorem row_3583 :
    (3583 : ℕ).Prime ∧ logScale (3583 : ℚ) = 11 ∧
      (81839557144 : ℤ) = ⌊logCenter (3583 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3583 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3583 : Reach 3583 35157125615327 146083174549 := by
  have hr := row_3583
  have hl := log_bounds hr.1
    (by change logScale (3583 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3581) (T := 35075286058183) (U := 146042403358)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3581

theorem row_3593 :
    (3593 : ℕ).Prime ∧ logScale (3593 : ℚ) = 11 ∧
      (81867427842 : ℤ) = ⌊logCenter (3593 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3593 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3593 : Reach 3593 35238993043169 146123843585 := by
  have hr := row_3593
  have hl := log_bounds hr.1
    (by change logScale (3593 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3583) (T := 35157125615327) (U := 146083174549)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3583

theorem row_3607 :
    (3607 : ℕ).Prime ∧ logScale (3607 : ℚ) = 11 ∧
      (81906316780 : ℤ) = ⌊logCenter (3607 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3607 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3607 : Reach 3607 35320899359949 146164366005 := by
  have hr := row_3607
  have hl := log_bounds hr.1
    (by change logScale (3607 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3593) (T := 35238993043169) (U := 146123843585)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3593

theorem row_3613 :
    (3613 : ℕ).Prime ∧ logScale (3613 : ℚ) = 11 ∧
      (81922937282 : ℤ) = ⌊logCenter (3613 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3613 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3613 : Reach 3613 35402822297231 146204832331 := by
  have hr := row_3613
  have hl := log_bounds hr.1
    (by change logScale (3613 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3607) (T := 35320899359949) (U := 146164366005)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3607

theorem row_3617 :
    (3617 : ℕ).Prime ∧ logScale (3617 : ℚ) = 11 ∧
      (81934002290 : ℤ) = ⌊logCenter (3617 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3617 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3617 : Reach 3617 35484756299521 146245265084 := by
  have hr := row_3617
  have hl := log_bounds hr.1
    (by change logScale (3617 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3613) (T := 35402822297231) (U := 146204832331)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3613

theorem row_3623 :
    (3623 : ℕ).Prime ∧ logScale (3623 : ℚ) = 11 ∧
      (81950576880 : ℤ) = ⌊logCenter (3623 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3623 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3623 : Reach 3623 35566706876401 146285642021 := by
  have hr := row_3623
  have hl := log_bounds hr.1
    (by change logScale (3623 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3617) (T := 35484756299521) (U := 146245265084)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3617

theorem row_3631 :
    (3631 : ℕ).Prime ∧ logScale (3631 : ℚ) = 11 ∧
      (81972633685 : ℤ) = ⌊logCenter (3631 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3631 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3631 : Reach 3631 35648679510086 146325941096 := by
  have hr := row_3631
  have hl := log_bounds hr.1
    (by change logScale (3631 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3623) (T := 35566706876401) (U := 146285642021)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3623

#print axioms reach_3631

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
