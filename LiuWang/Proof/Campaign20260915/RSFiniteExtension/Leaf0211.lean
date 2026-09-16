import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0210

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5431 :
    (5431 : ℕ).Prime ∧ logScale (5431 : ℚ) = 12 ∧
      (85998785549 : ℤ) = ⌊logCenter (5431 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5431 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5431 : Reach 5431 53225306474680 153345232712 := by
  have hr := row_5431
  have hl := log_bounds hr.1
    (by change logScale (5431 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5419) (T := 53139307689131) (U := 153316997537)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5419

theorem row_5437 :
    (5437 : ℕ).Prime ∧ logScale (5437 : ℚ) = 12 ∧
      (86009827140 : ℤ) = ⌊logCenter (5437 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5437 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5437 : Reach 5437 53311316301820 153373441916 := by
  have hr := row_5437
  have hl := log_bounds hr.1
    (by change logScale (5437 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5431) (T := 53225306474680) (U := 153345232712)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5431

theorem row_5441 :
    (5441 : ℕ).Prime ∧ logScale (5441 : ℚ) = 12 ∧
      (86017181433 : ℤ) = ⌊logCenter (5441 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5441 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5441 : Reach 5441 53397333483253 153401635564 := by
  have hr := row_5441
  have hl := log_bounds hr.1
    (by change logScale (5441 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5437) (T := 53311316301820) (U := 153373441916)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5437

theorem row_5443 :
    (5443 : ℕ).Prime ∧ logScale (5443 : ℚ) = 12 ∧
      (86020856553 : ℤ) = ⌊logCenter (5443 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5443 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5443 : Reach 5443 53483354339806 153429824031 := by
  have hr := row_5443
  have hl := log_bounds hr.1
    (by change logScale (5443 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5441) (T := 53397333483253) (U := 153401635564)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5441

theorem row_5449 :
    (5449 : ℕ).Prime ∧ logScale (5449 : ℚ) = 12 ∧
      (86031873814 : ℤ) = ⌊logCenter (5449 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5449 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5449 : Reach 5449 53569386213620 153457986628 := by
  have hr := row_5449
  have hl := log_bounds hr.1
    (by change logScale (5449 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5443) (T := 53483354339806) (U := 153429824031)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5443

theorem row_5471 :
    (5471 : ℕ).Prime ∧ logScale (5471 : ℚ) = 12 ∧
      (86072166909 : ℤ) = ⌊logCenter (5471 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5471 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5471 : Reach 5471 53655458380529 153486041105 := by
  have hr := row_5471
  have hl := log_bounds hr.1
    (by change logScale (5471 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5449) (T := 53569386213620) (U := 153457986628)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5449

theorem row_5477 :
    (5477 : ℕ).Prime ∧ logScale (5477 : ℚ) = 12 ∧
      (86083127816 : ℤ) = ⌊logCenter (5477 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5477 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5477 : Reach 5477 53741541508345 153514069966 := by
  have hr := row_5477
  have hl := log_bounds hr.1
    (by change logScale (5477 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5471) (T := 53655458380529) (U := 153486041105)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5471

theorem row_5479 :
    (5479 : ℕ).Prime ∧ logScale (5479 : ℚ) = 12 ∧
      (86086778784 : ℤ) = ⌊logCenter (5479 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5479 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5479 : Reach 5479 53827628287129 153542093711 := by
  have hr := row_5479
  have hl := log_bounds hr.1
    (by change logScale (5479 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5477) (T := 53741541508345) (U := 153514069966)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5477

#print axioms reach_5479

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
