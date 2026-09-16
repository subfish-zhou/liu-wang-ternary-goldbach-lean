import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0610
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14293 : PrimeGap 14281 14293 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14293 :
    (14293 : ℕ).Prime ∧ logScale (14293 : ℚ) = 13 ∧
      (95675251825 : ℤ) = ⌊logCenter (14293 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14293 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14293 : Reach 14293 141062121988134 170493215658 := by
  have hr := row_14293
  have hl := log_bounds hr.1
    (by change logScale (14293 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14281) (T := 140966446736309) (U := 170481287216)
    (by norm_num) (by norm_num) hr.1 gap_14293
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14281

theorem gap_14303 : PrimeGap 14293 14303 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 79, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14303 :
    (14303 : ℕ).Prime ∧ logScale (14303 : ℚ) = 13 ∧
      (95682245810 : ℤ) = ⌊logCenter (14303 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14303 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14303 : Reach 14303 141157804233944 170505136594 := by
  have hr := row_14303
  have hl := log_bounds hr.1
    (by change logScale (14303 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14293) (T := 141062121988134) (U := 170493215658)
    (by norm_num) (by norm_num) hr.1 gap_14303
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14293

theorem gap_14321 : PrimeGap 14303 14321 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 41, 2, 11, 2, 3, 2, 5, 2, 103, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14321 :
    (14321 : ℕ).Prime ∧ logScale (14321 : ℚ) = 13 ∧
      (95694822670 : ℤ) = ⌊logCenter (14321 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14321 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14321 : Reach 14321 141253499056614 170517043378 := by
  have hr := row_14321
  have hl := log_bounds hr.1
    (by change logScale (14321 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14303) (T := 141157804233944) (U := 170505136594)
    (by norm_num) (by norm_num) hr.1 gap_14321
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14303

theorem gap_14323 : PrimeGap 14321 14323 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14323 :
    (14323 : ℕ).Prime ∧ logScale (14323 : ℚ) = 13 ∧
      (95696219124 : ℤ) = ⌊logCenter (14323 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14323 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14323 : Reach 14323 141349195275738 170528949330 := by
  have hr := row_14323
  have hl := log_bounds hr.1
    (by change logScale (14323 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14321) (T := 141253499056614) (U := 170517043378)
    (by norm_num) (by norm_num) hr.1 gap_14323
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14321

theorem gap_14327 : PrimeGap 14323 14327 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14327 :
    (14327 : ℕ).Prime ∧ logScale (14327 : ℚ) = 13 ∧
      (95699011445 : ℤ) = ⌊logCenter (14327 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14327 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14327 : Reach 14327 141444894287183 170540852789 := by
  have hr := row_14327
  have hl := log_bounds hr.1
    (by change logScale (14327 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14323) (T := 141349195275738) (U := 170528949330)
    (by norm_num) (by norm_num) hr.1 gap_14327
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14323

theorem gap_14341 : PrimeGap 14327 14341 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14341 :
    (14341 : ℕ).Prime ∧ logScale (14341 : ℚ) = 13 ∧
      (95708778433 : ℤ) = ⌊logCenter (14341 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14341 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14341 : Reach 14341 141540603065616 170552745457 := by
  have hr := row_14341
  have hl := log_bounds hr.1
    (by change logScale (14341 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14327) (T := 141444894287183) (U := 170540852789)
    (by norm_num) (by norm_num) hr.1 gap_14341
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14327

theorem gap_14347 : PrimeGap 14341 14347 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14347 :
    (14347 : ℕ).Prime ∧ logScale (14347 : ℚ) = 13 ∧
      (95712961367 : ℤ) = ⌊logCenter (14347 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14347 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14347 : Reach 14347 141636316026983 170564633980 := by
  have hr := row_14347
  have hl := log_bounds hr.1
    (by change logScale (14347 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14341) (T := 141540603065616) (U := 170552745457)
    (by norm_num) (by norm_num) hr.1 gap_14347
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14341

theorem gap_14369 : PrimeGap 14347 14369 :=
  (primeGap_of_factors (ds := [2, 3, 2, 113, 2, 31, 2, 3, 2, 7, 2, 83, 2, 3, 2, 53, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14369 :
    (14369 : ℕ).Prime ∧ logScale (14369 : ℚ) = 13 ∧
      (95728283838 : ℤ) = ⌊logCenter (14369 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14369 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14369 : Reach 14369 141732044310821 170576505127 := by
  have hr := row_14369
  have hl := log_bounds hr.1
    (by change logScale (14369 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14347) (T := 141636316026983) (U := 170564633980)
    (by norm_num) (by norm_num) hr.1 gap_14369
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14347

#print axioms reach_14369

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
