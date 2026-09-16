import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0151

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4241 :
    (4241 : ℕ).Prime ∧ logScale (4241 : ℚ) = 12 ∧
      (83525543663 : ℤ) = ⌊logCenter (4241 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4241 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4241 : Reach 4241 41691226378237 149069521464 := by
  have hr := row_4241
  have hl := log_bounds hr.1
    (by change logScale (4241 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4231) (T := 41607700834574) (U := 149034371847)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4231

theorem row_4243 :
    (4243 : ℕ).Prime ∧ logScale (4243 : ℚ) = 12 ∧
      (83530258420 : ℤ) = ⌊logCenter (4243 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4243 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4243 : Reach 4243 41774756636657 149104662794 := by
  have hr := row_4243
  have hl := log_bounds hr.1
    (by change logScale (4243 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4241) (T := 41691226378237) (U := 149069521464)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4241

theorem row_4253 :
    (4253 : ℕ).Prime ∧ logScale (4253 : ℚ) = 12 ∧
      (83553798921 : ℤ) = ⌊logCenter (4253 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4253 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4253 : Reach 4253 41858310435578 149139729742 := by
  have hr := row_4253
  have hl := log_bounds hr.1
    (by change logScale (4253 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4243) (T := 41774756636657) (U := 149104662794)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4243

theorem row_4259 :
    (4259 : ℕ).Prime ∧ logScale (4259 : ℚ) = 12 ∧
      (83567896668 : ℤ) = ⌊logCenter (4259 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4259 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4259 : Reach 4259 41941878332246 149174755513 := by
  have hr := row_4259
  have hl := log_bounds hr.1
    (by change logScale (4259 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4253) (T := 41858310435578) (U := 149139729742)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4253

theorem row_4261 :
    (4261 : ℕ).Prime ∧ logScale (4261 : ℚ) = 12 ∧
      (83572591503 : ℤ) = ⌊logCenter (4261 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4261 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4261 : Reach 4261 42025450923749 149209773062 := by
  have hr := row_4261
  have hl := log_bounds hr.1
    (by change logScale (4261 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4259) (T := 41941878332246) (U := 149174755513)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4259

theorem row_4271 :
    (4271 : ℕ).Prime ∧ logScale (4271 : ℚ) = 12 ∧
      (83596032677 : ℤ) = ⌊logCenter (4271 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4271 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4271 : Reach 4271 42109046956426 149244716803 := by
  have hr := row_4271
  have hl := log_bounds hr.1
    (by change logScale (4271 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4261) (T := 42025450923749) (U := 149209773062)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4261

theorem row_4273 :
    (4273 : ℕ).Prime ∧ logScale (4273 : ℚ) = 12 ∧
      (83600714325 : ℤ) = ⌊logCenter (4273 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4273 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4273 : Reach 4273 42192647670751 149279652365 := by
  have hr := row_4273
  have hl := log_bounds hr.1
    (by change logScale (4273 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4271) (T := 42109046956426) (U := 149244716803)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4271

theorem row_4283 :
    (4283 : ℕ).Prime ∧ logScale (4283 : ℚ) = 12 ∧
      (83624089744 : ℤ) = ⌊logCenter (4283 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4283 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4283 : Reach 4283 42276271760495 149314514498 := by
  have hr := row_4283
  have hl := log_bounds hr.1
    (by change logScale (4283 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4273) (T := 42192647670751) (U := 149279652365)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4273

#print axioms reach_4283

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
