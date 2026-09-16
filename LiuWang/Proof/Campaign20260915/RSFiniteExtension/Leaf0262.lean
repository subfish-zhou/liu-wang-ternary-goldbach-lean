import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0261

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_6547 :
    (6547 : ℕ).Prime ∧ logScale (6547 : ℚ) = 12 ∧
      (87867622053 : ℤ) = ⌊logCenter (6547 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6547 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6547 : Reach 6547 64352609191242 156677968509 := by
  have hr := row_6547
  have hl := log_bounds hr.1
    (by change logScale (6547 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6529) (T := 64264741569189) (U := 156654037247)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6529

theorem row_6551 :
    (6551 : ℕ).Prime ∧ logScale (6551 : ℚ) = 12 ∧
      (87873729856 : ℤ) = ⌊logCenter (6551 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6551 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6551 : Reach 6551 64440482921098 156701888810 := by
  have hr := row_6551
  have hl := log_bounds hr.1
    (by change logScale (6551 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6547) (T := 64352609191242) (U := 156677968509)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6547

theorem row_6553 :
    (6553 : ℕ).Prime ∧ logScale (6553 : ℚ) = 12 ∧
      (87876782359 : ℤ) = ⌊logCenter (6553 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6553 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6553 : Reach 6553 64528359703457 156725805460 := by
  have hr := row_6553
  have hl := log_bounds hr.1
    (by change logScale (6553 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6551) (T := 64440482921098) (U := 156701888810)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6551

theorem row_6563 :
    (6563 : ℕ).Prime ∧ logScale (6563 : ℚ) = 12 ∧
      (87892030913 : ℤ) = ⌊logCenter (6563 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6563 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6563 : Reach 6563 64616251734370 156749689308 := by
  have hr := row_6563
  have hl := log_bounds hr.1
    (by change logScale (6563 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6553) (T := 64528359703457) (U := 156725805460)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6553

theorem row_6569 :
    (6569 : ℕ).Prime ∧ logScale (6569 : ℚ) = 12 ∧
      (87901168897 : ℤ) = ⌊logCenter (6569 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6569 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6569 : Reach 6569 64704152903267 156773554974 := by
  have hr := row_6569
  have hl := log_bounds hr.1
    (by change logScale (6569 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6563) (T := 64616251734370) (U := 156749689308)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6563

theorem row_6571 :
    (6571 : ℕ).Prime ∧ logScale (6571 : ℚ) = 12 ∧
      (87904213037 : ℤ) = ⌊logCenter (6571 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6571 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6571 : Reach 6571 64792057116304 156797417007 := by
  have hr := row_6571
  have hl := log_bounds hr.1
    (by change logScale (6571 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6569) (T := 64704152903267) (U := 156773554974)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6569

theorem row_6577 :
    (6577 : ℕ).Prime ∧ logScale (6577 : ℚ) = 12 ∧
      (87913339901 : ℤ) = ⌊logCenter (6577 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6577 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6577 : Reach 6577 64879970456205 156821260897 := by
  have hr := row_6577
  have hl := log_bounds hr.1
    (by change logScale (6577 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6571) (T := 64792057116304) (U := 156797417007)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6571

theorem row_6581 :
    (6581 : ℕ).Prime ∧ logScale (6581 : ℚ) = 12 ∧
      (87919419853 : ℤ) = ⌊logCenter (6581 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6581 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6581 : Reach 6581 64967889876058 156845093916 := by
  have hr := row_6581
  have hl := log_bounds hr.1
    (by change logScale (6581 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6577) (T := 64879970456205) (U := 156821260897)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6577

#print axioms reach_6581

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
