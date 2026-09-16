import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0150

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4159 :
    (4159 : ℕ).Prime ∧ logScale (4159 : ℚ) = 12 ∧
      (83330299366 : ℤ) = ⌊logCenter (4159 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4159 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4159 : Reach 4159 41023500544616 148786869481 := by
  have hr := row_4159
  have hl := log_bounds hr.1
    (by change logScale (4159 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4157) (T := 40940170245250) (U := 148751094806)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4157

theorem row_4177 :
    (4177 : ℕ).Prime ∧ logScale (4177 : ℚ) = 12 ∧
      (83373485613 : ℤ) = ⌊logCenter (4177 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4177 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4177 : Reach 4177 41106874030229 148822498521 := by
  have hr := row_4177
  have hl := log_bounds hr.1
    (by change logScale (4177 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4159) (T := 41023500544616) (U := 148786869481)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4159

theorem row_4201 :
    (4201 : ℕ).Prime ∧ logScale (4201 : ℚ) = 12 ∧
      (83430778680 : ℤ) = ⌊logCenter (4201 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4201 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4201 : Reach 4201 41190304808909 148857932450 := by
  have hr := row_4201
  have hl := log_bounds hr.1
    (by change logScale (4201 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4177) (T := 41106874030229) (U := 148822498521)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4177

theorem row_4211 :
    (4211 : ℕ).Prime ∧ logScale (4211 : ℚ) = 12 ∧
      (83454554250 : ℤ) = ⌊logCenter (4211 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4211 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4211 : Reach 4211 41273759363159 148893290629 := by
  have hr := row_4211
  have hl := log_bounds hr.1
    (by change logScale (4211 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4201) (T := 41190304808909) (U := 148857932450)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4201

theorem row_4217 :
    (4217 : ℕ).Prime ∧ logScale (4217 : ℚ) = 12 ∧
      (83468792506 : ℤ) = ⌊logCenter (4217 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4217 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4217 : Reach 4217 41357228155665 148928606875 := by
  have hr := row_4217
  have hl := log_bounds hr.1
    (by change logScale (4217 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4211) (T := 41273759363159) (U := 148893290629)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4211

theorem row_4219 :
    (4219 : ℕ).Prime ∧ logScale (4219 : ℚ) = 12 ∧
      (83473534090 : ℤ) = ⌊logCenter (4219 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4219 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4219 : Reach 4219 41440701689755 148963914748 := by
  have hr := row_4219
  have hl := log_bounds hr.1
    (by change logScale (4219 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4217) (T := 41357228155665) (U := 148928606875)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4217

theorem row_4229 :
    (4229 : ℕ).Prime ∧ logScale (4229 : ℚ) = 12 ∧
      (83497208343 : ℤ) = ⌊logCenter (4229 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4229 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4229 : Reach 4229 41524198898098 148999147462 := by
  have hr := row_4229
  have hl := log_bounds hr.1
    (by change logScale (4229 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4219) (T := 41440701689755) (U := 148963914748)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4219

theorem row_4231 :
    (4231 : ℕ).Prime ∧ logScale (4231 : ℚ) = 12 ∧
      (83501936476 : ℤ) = ⌊logCenter (4231 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4231 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4231 : Reach 4231 41607700834574 149034371847 := by
  have hr := row_4231
  have hl := log_bounds hr.1
    (by change logScale (4231 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4229) (T := 41524198898098) (U := 148999147462)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4229

#print axioms reach_4231

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
