import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0051

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2293 :
    (2293 : ℕ).Prime ∧ logScale (2293 : ℚ) = 11 ∧
      (77376162799 : ℤ) = ⌊logCenter (2293 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2293 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2293 : Reach 2293 22313578334974 138164658694 := by
  have hr := row_2293
  have hl := log_bounds hr.1
    (by change logScale (2293 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2287) (T := 22236202172175) (U := 138104403718)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2287

theorem row_2297 :
    (2297 : ℕ).Prime ∧ logScale (2297 : ℚ) = 11 ∧
      (77393591998 : ℤ) = ⌊logCenter (2297 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2297 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2297 : Reach 2297 22390971926972 138224834940 := by
  have hr := row_2297
  have hl := log_bounds hr.1
    (by change logScale (2297 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2293) (T := 22313578334974) (U := 138164658694)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2293

theorem row_2309 :
    (2309 : ℕ).Prime ∧ logScale (2309 : ℚ) = 11 ∧
      (77445698064 : ℤ) = ⌊logCenter (2309 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2309 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2309 : Reach 2309 22468417625036 138284724384 := by
  have hr := row_2309
  have hl := log_bounds hr.1
    (by change logScale (2309 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2297) (T := 22390971926972) (U := 138224834940)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2297

theorem row_2311 :
    (2311 : ℕ).Prime ∧ logScale (2311 : ℚ) = 11 ∧
      (77454356074 : ℤ) = ⌊logCenter (2311 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2311 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2311 : Reach 2311 22545871981110 138344587902 := by
  have hr := row_2311
  have hl := log_bounds hr.1
    (by change logScale (2311 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2309) (T := 22468417625036) (U := 138284724384)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2309

theorem row_2333 :
    (2333 : ℕ).Prime ∧ logScale (2333 : ℚ) = 11 ∧
      (77549102691 : ℤ) = ⌊logCenter (2333 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2333 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2333 : Reach 2333 22623421083801 138403912340 := by
  have hr := row_2333
  have hl := log_bounds hr.1
    (by change logScale (2333 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2311) (T := 22545871981110) (U := 138344587902)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2311

theorem row_2339 :
    (2339 : ℕ).Prime ∧ logScale (2339 : ℚ) = 11 ∧
      (77574787637 : ℤ) = ⌊logCenter (2339 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2339 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2339 : Reach 2339 22700995871438 138463109908 := by
  have hr := row_2339
  have hl := log_bounds hr.1
    (by change logScale (2339 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2333) (T := 22623421083801) (U := 138403912340)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2333

theorem row_2341 :
    (2341 : ℕ).Prime ∧ logScale (2341 : ℚ) = 11 ∧
      (77583334646 : ℤ) = ⌊logCenter (2341 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2341 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2341 : Reach 2341 22778579206084 138522282178 := by
  have hr := row_2341
  have hl := log_bounds hr.1
    (by change logScale (2341 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2339) (T := 22700995871438) (U := 138463109908)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2339

theorem row_2347 :
    (2347 : ℕ).Prime ∧ logScale (2347 : ℚ) = 11 ∧
      (77608931929 : ℤ) = ⌊logCenter (2347 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2347 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2347 : Reach 2347 22856188138013 138581328335 := by
  have hr := row_2347
  have hl := log_bounds hr.1
    (by change logScale (2347 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2341) (T := 22778579206084) (U := 138522282178)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2341

#print axioms reach_2347

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
