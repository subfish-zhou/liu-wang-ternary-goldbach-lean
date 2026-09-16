import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2153 :
    (2153 : ℕ).Prime ∧ logScale (2153 : ℚ) = 11 ∧
      (76746174945 : ℤ) = ⌊logCenter (2153 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2153 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2153 : Reach 2153 21079395843238 137180344540 := by
  have hr := row_2153
  have hl := log_bounds hr.1
    (by change logScale (2153 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2143) (T := 21002649668293) (U := 137116628634)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2143

theorem row_2161 :
    (2161 : ℕ).Prime ∧ logScale (2161 : ℚ) = 11 ∧
      (76783263536 : ℤ) = ⌊logCenter (2161 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2161 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2161 : Reach 2161 21156179106774 137243853959 := by
  have hr := row_2161
  have hl := log_bounds hr.1
    (by change logScale (2161 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2153) (T := 21079395843238) (U := 137180344540)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2153

theorem row_2179 :
    (2179 : ℕ).Prime ∧ logScale (2179 : ℚ) = 11 ∧
      (76866213320 : ℤ) = ⌊logCenter (2179 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2179 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2179 : Reach 2179 21233045320094 137306867667 := by
  have hr := row_2179
  have hl := log_bounds hr.1
    (by change logScale (2179 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2161) (T := 21156179106774) (U := 137243853959)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2161

theorem row_2203 :
    (2203 : ℕ).Prime ∧ logScale (2203 : ℚ) = 11 ∧
      (76975753439 : ℤ) = ⌊logCenter (2203 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2203 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2203 : Reach 2203 21310021073533 137369223193 := by
  have hr := row_2203
  have hl := log_bounds hr.1
    (by change logScale (2203 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2179) (T := 21233045320094) (U := 137306867667)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2179

theorem row_2207 :
    (2207 : ℕ).Prime ∧ logScale (2207 : ℚ) = 11 ∧
      (76993894033 : ℤ) = ⌊logCenter (2207 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2207 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2207 : Reach 2207 21387014967566 137431493920 := by
  have hr := row_2207
  have hl := log_bounds hr.1
    (by change logScale (2207 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2203) (T := 21310021073533) (U := 137369223193)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2203

theorem row_2213 :
    (2213 : ℕ).Prime ∧ logScale (2213 : ℚ) = 11 ∧
      (77021043371 : ℤ) = ⌊logCenter (2213 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2213 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2213 : Reach 2213 21464036010937 137493623891 := by
  have hr := row_2213
  have hl := log_bounds hr.1
    (by change logScale (2213 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2207) (T := 21387014967566) (U := 137431493920)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2207

theorem row_2221 :
    (2221 : ℕ).Prime ∧ logScale (2221 : ℚ) = 11 ∧
      (77057128210 : ℤ) = ⌊logCenter (2221 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2221 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2221 : Reach 2221 21541093139147 137555557956 := by
  have hr := row_2221
  have hl := log_bounds hr.1
    (by change logScale (2221 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2213) (T := 21464036010937) (U := 137493623891)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2213

theorem row_2237 :
    (2237 : ℕ).Prime ∧ logScale (2237 : ℚ) = 11 ∧
      (77128909586 : ℤ) = ⌊logCenter (2237 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2237 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2237 : Reach 2237 21618222048733 137617076542 := by
  have hr := row_2237
  have hl := log_bounds hr.1
    (by change logScale (2237 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2221) (T := 21541093139147) (U := 137555557956)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2221

#print axioms reach_2237

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
