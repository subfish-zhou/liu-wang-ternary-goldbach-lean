import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0071

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2683 :
    (2683 : ℕ).Prime ∧ logScale (2683 : ℚ) = 11 ∧
      (78946908475 : ℤ) = ⌊logCenter (2683 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2683 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2683 : Reach 2683 26065873142101 140864989183 := by
  have hr := row_2683
  have hl := log_bounds hr.1
    (by change logScale (2683 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2677) (T := 25986926233626) (U := 140812486391)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2677

theorem row_2687 :
    (2687 : ℕ).Prime ∧ logScale (2687 : ℚ) = 11 ∧
      (78961806057 : ℤ) = ⌊logCenter (2687 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2687 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2687 : Reach 2687 26144834948158 140917433334 := by
  have hr := row_2687
  have hl := log_bounds hr.1
    (by change logScale (2687 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2683) (T := 26065873142101) (U := 140864989183)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2683

theorem row_2689 :
    (2689 : ℕ).Prime ∧ logScale (2689 : ℚ) = 11 ∧
      (78969246534 : ℤ) = ⌊logCenter (2689 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2689 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2689 : Reach 2689 26223804194692 140969857975 := by
  have hr := row_2689
  have hl := log_bounds hr.1
    (by change logScale (2689 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2687) (T := 26144834948158) (U := 140917433334)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2687

theorem row_2693 :
    (2693 : ℕ).Prime ∧ logScale (2693 : ℚ) = 11 ∧
      (78984110899 : ℤ) = ⌊logCenter (2693 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2693 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2693 : Reach 2693 26302788305591 141022224193 := by
  have hr := row_2693
  have hl := log_bounds hr.1
    (by change logScale (2693 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2689) (T := 26223804194692) (U := 140969857975)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2689

theorem row_2699 :
    (2699 : ℕ).Prime ∧ logScale (2699 : ℚ) = 11 ∧
      (79006366101 : ℤ) = ⌊logCenter (2699 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2699 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2699 : Reach 2699 26381794671692 141074493365 := by
  have hr := row_2699
  have hl := log_bounds hr.1
    (by change logScale (2699 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2693) (T := 26302788305591) (U := 141022224193)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2693

theorem row_2707 :
    (2707 : ℕ).Prime ∧ logScale (2707 : ℚ) = 11 ∧
      (79035962867 : ℤ) = ⌊logCenter (2707 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2707 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2707 : Reach 2707 26460830634559 141126627325 := by
  have hr := row_2707
  have hl := log_bounds hr.1
    (by change logScale (2707 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2699) (T := 26381794671692) (U := 141074493365)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2699

theorem row_2711 :
    (2711 : ℕ).Prime ∧ logScale (2711 : ℚ) = 11 ∧
      (79050728466 : ℤ) = ⌊logCenter (2711 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2711 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2711 : Reach 2711 26539881363025 141178703572 := by
  have hr := row_2711
  have hl := log_bounds hr.1
    (by change logScale (2711 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2707) (T := 26460830634559) (U := 141126627325)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2707

theorem row_2713 :
    (2713 : ℕ).Prime ∧ logScale (2713 : ℚ) = 11 ∧
      (79058103097 : ℤ) = ⌊logCenter (2713 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2713 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2713 : Reach 2713 26618939466122 141230760617 := by
  have hr := row_2713
  have hl := log_bounds hr.1
    (by change logScale (2713 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2711) (T := 26539881363025) (U := 141178703572)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2711

#print axioms reach_2713

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
