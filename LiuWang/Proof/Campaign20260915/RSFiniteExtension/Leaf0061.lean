import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0060

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2399 :
    (2399 : ℕ).Prime ∧ logScale (2399 : ℚ) = 11 ∧
      (77828072599 : ℤ) = ⌊logCenter (2399 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2399 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2399 : Reach 2399 23555843481017 139106966423 := by
  have hr := row_2399
  have hl := log_bounds hr.1
    (by change logScale (2399 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2393) (T := 23478015408418) (U := 139048981026)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2393

theorem row_2411 :
    (2411 : ℕ).Prime ∧ logScale (2411 : ℚ) = 11 ∧
      (77877968753 : ℤ) = ⌊logCenter (2411 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2411 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2411 : Reach 2411 23633721449770 139164687156 := by
  have hr := row_2411
  have hl := log_bounds hr.1
    (by change logScale (2411 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2399) (T := 23555843481017) (U := 139106966423)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2399

theorem row_2417 :
    (2417 : ℕ).Prime ∧ logScale (2417 : ℚ) = 11 ∧
      (77902823778 : ℤ) = ⌊logCenter (2417 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2417 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2417 : Reach 2417 23711624273548 139222288434 := by
  have hr := row_2417
  have hl := log_bounds hr.1
    (by change logScale (2417 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2411) (T := 23633721449770) (U := 139164687156)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2411

theorem row_2423 :
    (2423 : ℕ).Prime ∧ logScale (2423 : ℚ) = 11 ∧
      (77927617179 : ℤ) = ⌊logCenter (2423 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2423 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2423 : Reach 2423 23789551890727 139279770800 := by
  have hr := row_2423
  have hl := log_bounds hr.1
    (by change logScale (2423 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2417) (T := 23711624273548) (U := 139222288434)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2417

theorem row_2437 :
    (2437 : ℕ).Prime ∧ logScale (2437 : ℚ) = 11 ∧
      (77985230507 : ℤ) = ⌊logCenter (2437 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2437 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2437 : Reach 2437 23867537121234 139336946404 := by
  have hr := row_2437
  have hl := log_bounds hr.1
    (by change logScale (2437 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2423) (T := 23789551890727) (U := 139279770800)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2423

theorem row_2441 :
    (2441 : ℕ).Prime ∧ logScale (2441 : ℚ) = 11 ∧
      (78001630675 : ℤ) = ⌊logCenter (2441 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2441 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2441 : Reach 2441 23945538751909 139394051710 := by
  have hr := row_2441
  have hl := log_bounds hr.1
    (by change logScale (2441 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2437) (T := 23867537121234) (U := 139336946404)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2437

theorem row_2447 :
    (2447 : ℕ).Prime ∧ logScale (2447 : ℚ) = 11 ∧
      (78026180605 : ℤ) = ⌊logCenter (2447 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2447 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2447 : Reach 2447 24023564932514 139451040284 := by
  have hr := row_2447
  have hl := log_bounds hr.1
    (by change logScale (2447 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2441) (T := 23945538751909) (U := 139394051710)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2441

theorem row_2459 :
    (2459 : ℕ).Prime ∧ logScale (2459 : ℚ) = 11 ∧
      (78075100393 : ℤ) = ⌊logCenter (2459 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2459 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2459 : Reach 2459 24101640032907 139507773824 := by
  have hr := row_2459
  have hl := log_bounds hr.1
    (by change logScale (2459 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2447) (T := 24023564932514) (U := 139451040284)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2447

#print axioms reach_2459

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
