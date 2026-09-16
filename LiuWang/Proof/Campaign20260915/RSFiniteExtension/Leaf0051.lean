import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0050

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2239 :
    (2239 : ℕ).Prime ∧ logScale (2239 : ℚ) = 11 ∧
      (77137846137 : ℤ) = ⌊logCenter (2239 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2239 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2239 : Reach 2239 21695359894870 137678567640 := by
  have hr := row_2239
  have hl := log_bounds hr.1
    (by change logScale (2239 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2237) (T := 21618222048733) (U := 137617076542)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2237

theorem row_2243 :
    (2243 : ℕ).Prime ∧ logScale (2243 : ℚ) = 11 ∧
      (77155695316 : ℤ) = ⌊logCenter (2243 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2243 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2243 : Reach 2243 21772515590186 137739976457 := by
  have hr := row_2243
  have hl := log_bounds hr.1
    (by change logScale (2243 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2239) (T := 21695359894870) (U := 137678567640)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2239

theorem row_2251 :
    (2251 : ℕ).Prime ∧ logScale (2251 : ℚ) = 11 ∧
      (77191298380 : ℤ) = ⌊logCenter (2251 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2251 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2251 : Reach 2251 21849706888566 137801194225 := by
  have hr := row_2251
  have hl := log_bounds hr.1
    (by change logScale (2251 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2243) (T := 21772515590186) (U := 137739976457)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2243

theorem row_2267 :
    (2267 : ℕ).Prime ∧ logScale (2267 : ℚ) = 11 ∧
      (77262126476 : ℤ) = ⌊logCenter (2267 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2267 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2267 : Reach 2267 21926969015042 137862006756 := by
  have hr := row_2267
  have hl := log_bounds hr.1
    (by change logScale (2267 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2251) (T := 21849706888566) (U := 137801194225)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2251

theorem row_2269 :
    (2269 : ℕ).Prime ∧ logScale (2269 : ℚ) = 11 ∧
      (77270944819 : ℤ) = ⌊logCenter (2269 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2269 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2269 : Reach 2269 22004239959861 137922792474 := by
  have hr := row_2269
  have hl := log_bounds hr.1
    (by change logScale (2269 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2267) (T := 21926969015042) (U := 137862006756)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2267

theorem row_2273 :
    (2273 : ℕ).Prime ∧ logScale (2273 : ℚ) = 11 ∧
      (77288558209 : ℤ) = ⌊logCenter (2273 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2273 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2273 : Reach 2273 22081528518070 137983497929 := by
  have hr := row_2273
  have hl := log_bounds hr.1
    (by change logScale (2273 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2269) (T := 22004239959861) (U := 137922792474)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2269

theorem row_2281 :
    (2281 : ℕ).Prime ∧ logScale (2281 : ℚ) = 11 ∧
      (77323692194 : ℤ) = ⌊logCenter (2281 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2281 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2281 : Reach 2281 22158852210264 138044017008 := by
  have hr := row_2281
  have hl := log_bounds hr.1
    (by change logScale (2281 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2273) (T := 22081528518070) (U := 137983497929)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2273

theorem row_2287 :
    (2287 : ℕ).Prime ∧ logScale (2287 : ℚ) = 11 ∧
      (77349961911 : ℤ) = ⌊logCenter (2287 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2287 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2287 : Reach 2287 22236202172175 138104403718 := by
  have hr := row_2287
  have hl := log_bounds hr.1
    (by change logScale (2287 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2281) (T := 22158852210264) (U := 138044017008)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2281

#print axioms reach_2287

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
