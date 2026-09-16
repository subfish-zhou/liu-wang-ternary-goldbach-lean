import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block017

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4723 :
    (4723 : ℕ).Prime ∧ logScale (4723 : ℚ) = 12 ∧
      (84601994667 : ℤ) = ⌊logCenter (4723 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4723 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4723 : Reach 4723 46399694469124 150944622212 := by
  have hr := row_4723
  have hl := log_bounds hr.1
    (by change logScale (4723 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4721) (T := 46315092474457) (U := 150912662732)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4721

theorem row_4729 :
    (4729 : ℕ).Prime ∧ logScale (4729 : ℚ) = 12 ∧
      (84614690395 : ℤ) = ⌊logCenter (4729 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4729 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4729 : Reach 4729 46484309159519 150976547894 := by
  have hr := row_4729
  have hl := log_bounds hr.1
    (by change logScale (4729 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4723) (T := 46399694469124) (U := 150944622212)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4723

theorem row_4733 :
    (4733 : ℕ).Prime ∧ logScale (4733 : ℚ) = 12 ∧
      (84623145267 : ℤ) = ⌊logCenter (4733 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4733 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4733 : Reach 4733 46568932304786 151008453336 := by
  have hr := row_4733
  have hl := log_bounds hr.1
    (by change logScale (4733 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4729) (T := 46484309159519) (U := 150976547894)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4729

theorem row_4751 :
    (4751 : ℕ).Prime ∧ logScale (4751 : ℚ) = 12 ∧
      (84661103980 : ℤ) = ⌊logCenter (4751 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4751 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4751 : Reach 4751 46653593408766 151040244590 := by
  have hr := row_4751
  have hl := log_bounds hr.1
    (by change logScale (4751 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4733) (T := 46568932304786) (U := 151008453336)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4733

theorem row_4759 :
    (4759 : ℕ).Prime ∧ logScale (4759 : ℚ) = 12 ∧
      (84677928380 : ℤ) = ⌊logCenter (4759 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4759 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4759 : Reach 4759 46738271337146 151071989072 := by
  have hr := row_4759
  have hl := log_bounds hr.1
    (by change logScale (4759 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4751) (T := 46653593408766) (U := 151040244590)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4751

theorem row_4783 :
    (4783 : ℕ).Prime ∧ logScale (4783 : ℚ) = 12 ∧
      (84728232405 : ℤ) = ⌊logCenter (4783 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4783 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4783 : Reach 4783 46822999569551 151103580873 := by
  have hr := row_4783
  have hl := log_bounds hr.1
    (by change logScale (4783 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4759) (T := 46738271337146) (U := 151071989072)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4759

theorem row_4787 :
    (4787 : ℕ).Prime ∧ logScale (4787 : ℚ) = 12 ∧
      (84736591862 : ℤ) = ⌊logCenter (4787 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4787 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4787 : Reach 4787 46907736161413 151135152871 := by
  have hr := row_4787
  have hl := log_bounds hr.1
    (by change logScale (4787 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4783) (T := 46822999569551) (U := 151103580873)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4783

theorem row_4789 :
    (4789 : ℕ).Prime ∧ logScale (4789 : ℚ) = 12 ∧
      (84740768972 : ℤ) = ⌊logCenter (4789 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4789 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4789 : Reach 4789 46992476930385 151166718275 := by
  have hr := row_4789
  have hl := log_bounds hr.1
    (by change logScale (4789 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4787) (T := 46907736161413) (U := 151135152871)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4787

#print axioms reach_4789

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
