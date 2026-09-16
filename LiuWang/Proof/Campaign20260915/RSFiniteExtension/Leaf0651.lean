import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0650
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15187 : PrimeGap 15173 15187 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 43, 2, 17, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15187 :
    (15187 : ℕ).Prime ∧ logScale (15187 : ℚ) = 13 ∧
      (96281950743 : ℤ) = ⌊logCenter (15187 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15187 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15187 : Reach 15187 150276184630926 171607822359 := by
  have hr := row_15187
  have hl := log_bounds hr.1
    (by change logScale (15187 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15173) (T := 150179902680183) (U := 171596522706)
    (by norm_num) (by norm_num) hr.1 gap_15187
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15173

theorem gap_15193 : PrimeGap 15187 15193 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15193 :
    (15193 : ℕ).Prime ∧ logScale (15193 : ℚ) = 13 ∧
      (96285900710 : ℤ) = ⌊logCenter (15193 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15193 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15193 : Reach 15193 150372470531636 171619118293 := by
  have hr := row_15193
  have hl := log_bounds hr.1
    (by change logScale (15193 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15187) (T := 150276184630926) (U := 171607822359)
    (by norm_num) (by norm_num) hr.1 gap_15193
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15187

theorem gap_15199 : PrimeGap 15193 15199 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15199 :
    (15199 : ℕ).Prime ∧ logScale (15199 : ℚ) = 13 ∧
      (96289849118 : ℤ) = ⌊logCenter (15199 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15199 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15199 : Reach 15199 150468760380754 171630410511 := by
  have hr := row_15199
  have hl := log_bounds hr.1
    (by change logScale (15199 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15193) (T := 150372470531636) (U := 171619118293)
    (by norm_num) (by norm_num) hr.1 gap_15199
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15193

theorem gap_15217 : PrimeGap 15199 15217 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15217 :
    (15217 : ℕ).Prime ∧ logScale (15217 : ℚ) = 13 ∧
      (96301684995 : ℤ) = ⌊logCenter (15217 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15217 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15217 : Reach 15217 150565062065749 171641690113 := by
  have hr := row_15217
  have hl := log_bounds hr.1
    (by change logScale (15217 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15199) (T := 150468760380754) (U := 171630410511)
    (by norm_num) (by norm_num) hr.1 gap_15217
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15199

theorem gap_15227 : PrimeGap 15217 15227 :=
  (primeGap_of_factors (ds := [2, 3, 2, 31, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15227 :
    (15227 : ℕ).Prime ∧ logScale (15227 : ℚ) = 13 ∧
      (96308254434 : ℤ) = ⌊logCenter (15227 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15227 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15227 : Reach 15227 150661370320183 171652963047 := by
  have hr := row_15227
  have hl := log_bounds hr.1
    (by change logScale (15227 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15217) (T := 150565062065749) (U := 171641690113)
    (by norm_num) (by norm_num) hr.1 gap_15227
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15217

theorem gap_15233 : PrimeGap 15227 15233 :=
  (primeGap_of_factors (ds := [2, 97, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15233 :
    (15233 : ℕ).Prime ∧ logScale (15233 : ℚ) = 13 ∧
      (96312194027 : ℤ) = ⌊logCenter (15233 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15233 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15233 : Reach 15233 150757682514210 171664232281 := by
  have hr := row_15233
  have hl := log_bounds hr.1
    (by change logScale (15233 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15227) (T := 150661370320183) (U := 171652963047)
    (by norm_num) (by norm_num) hr.1 gap_15233
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15227

theorem gap_15241 : PrimeGap 15233 15241 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15241 :
    (15241 : ℕ).Prime ∧ logScale (15241 : ℚ) = 13 ∧
      (96317444405 : ℤ) = ⌊logCenter (15241 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15241 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15241 : Reach 15241 150853999958615 171675496339 := by
  have hr := row_15241
  have hl := log_bounds hr.1
    (by change logScale (15241 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15233) (T := 150757682514210) (U := 171664232281)
    (by norm_num) (by norm_num) hr.1 gap_15241
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15233

theorem gap_15259 : PrimeGap 15241 15259 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 79, 2, 3, 2, 101, 2, 7, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15259 :
    (15259 : ℕ).Prime ∧ logScale (15259 : ℚ) = 13 ∧
      (96329247685 : ℤ) = ⌊logCenter (15259 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15259 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15259 : Reach 15259 150950329206300 171686747847 := by
  have hr := row_15259
  have hl := log_bounds hr.1
    (by change logScale (15259 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15241) (T := 150853999958615) (U := 171675496339)
    (by norm_num) (by norm_num) hr.1 gap_15259
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15241

#print axioms reach_15259

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
