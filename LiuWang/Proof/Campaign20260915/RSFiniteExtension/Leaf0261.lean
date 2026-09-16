import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0260

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_6449 :
    (6449 : ℕ).Prime ∧ logScale (6449 : ℚ) = 12 ∧
      (87716803558 : ℤ) = ⌊logCenter (6449 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6449 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6449 : Reach 6449 63650304006618 156485092543 := by
  have hr := row_6449
  have hl := log_bounds hr.1
    (by change logScale (6449 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6427) (T := 63562587203060) (U := 156460827526)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6427

theorem row_6451 :
    (6451 : ℕ).Prime ∧ logScale (6451 : ℚ) = 12 ∧
      (87719904334 : ℤ) = ⌊logCenter (6451 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6451 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6451 : Reach 6451 63738023910952 156509353798 := by
  have hr := row_6451
  have hl := log_bounds hr.1
    (by change logScale (6451 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6449) (T := 63650304006618) (U := 156485092543)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6449

theorem row_6469 :
    (6469 : ℕ).Prime ∧ logScale (6469 : ℚ) = 12 ∧
      (87747768129 : ℤ) = ⌊logCenter (6469 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6469 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6469 : Reach 6469 63825771679081 156533551287 := by
  have hr := row_6469
  have hl := log_bounds hr.1
    (by change logScale (6469 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6451) (T := 63738023910952) (U := 156509353798)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6451

theorem row_6473 :
    (6473 : ℕ).Prime ∧ logScale (6473 : ℚ) = 12 ∧
      (87753949554 : ℤ) = ⌊logCenter (6473 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6473 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6473 : Reach 6473 63913525628635 156557737559 := by
  have hr := row_6473
  have hl := log_bounds hr.1
    (by change logScale (6473 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6469) (T := 63825771679081) (U := 156533551287)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6469

theorem row_6481 :
    (6481 : ℕ).Prime ∧ logScale (6481 : ℚ) = 12 ∧
      (87766300953 : ℤ) = ⌊logCenter (6481 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6481 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6481 : Reach 6481 64001291929588 156581897704 := by
  have hr := row_6481
  have hl := log_bounds hr.1
    (by change logScale (6481 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6473) (T := 63913525628635) (U := 156557737559)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6473

theorem row_6491 :
    (6491 : ℕ).Prime ∧ logScale (6491 : ℚ) = 12 ∧
      (87781718779 : ℤ) = ⌊logCenter (6491 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6491 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6491 : Reach 6491 64089073648367 156606024345 := by
  have hr := row_6491
  have hl := log_bounds hr.1
    (by change logScale (6491 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6481) (T := 64001291929588) (U := 156581897704)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6481

theorem row_6521 :
    (6521 : ℕ).Prime ∧ logScale (6521 : ℚ) = 12 ∧
      (87827830142 : ℤ) = ⌊logCenter (6521 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6521 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6521 : Reach 6521 64176901478509 156630043674 := by
  have hr := row_6521
  have hl := log_bounds hr.1
    (by change logScale (6521 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6491) (T := 64089073648367) (U := 156606024345)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6491

theorem row_6529 :
    (6529 : ℕ).Prime ∧ logScale (6529 : ℚ) = 12 ∧
      (87840090680 : ℤ) = ⌊logCenter (6529 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6529 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6529 : Reach 6529 64264741569189 156654037247 := by
  have hr := row_6529
  have hl := log_bounds hr.1
    (by change logScale (6529 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6521) (T := 64176901478509) (U := 156630043674)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6521

#print axioms reach_6529

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
