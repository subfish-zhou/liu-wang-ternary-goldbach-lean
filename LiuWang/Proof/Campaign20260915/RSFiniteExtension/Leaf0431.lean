import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0430
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10141 : PrimeGap 10139 10141 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10141 :
    (10141 : ℕ).Prime ∧ logScale (10141 : ℚ) = 13 ∧
      (92243418882 : ℤ) = ⌊logCenter (10141 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10141 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10141 : Reach 10141 100434839822375 164505830756 := by
  have hr := row_10141
  have hl := log_bounds hr.1
    (by change logScale (10141 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10139) (T := 100342596403493) (U := 164489608901)
    (by norm_num) (by norm_num) hr.1 gap_10141
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10139

theorem gap_10151 : PrimeGap 10141 10151 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 73, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10151 :
    (10151 : ℕ).Prime ∧ logScale (10151 : ℚ) = 13 ∧
      (92253274984 : ℤ) = ⌊logCenter (10151 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10151 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10151 : Reach 10151 100527093097359 164522038228 := by
  have hr := row_10151
  have hl := log_bounds hr.1
    (by change logScale (10151 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10141) (T := 100434839822375) (U := 164505830756)
    (by norm_num) (by norm_num) hr.1 gap_10151
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10141

theorem gap_10159 : PrimeGap 10151 10159 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10159 :
    (10159 : ℕ).Prime ∧ logScale (10159 : ℚ) = 13 ∧
      (92261152877 : ℤ) = ⌊logCenter (10159 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10159 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10159 : Reach 10159 100619354250236 164538234531 := by
  have hr := row_10159
  have hl := log_bounds hr.1
    (by change logScale (10159 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10151) (T := 100527093097359) (U := 164522038228)
    (by norm_num) (by norm_num) hr.1 gap_10159
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10151

theorem gap_10163 : PrimeGap 10159 10163 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10163 :
    (10163 : ℕ).Prime ∧ logScale (10163 : ℚ) = 13 ∧
      (92265089497 : ℤ) = ⌊logCenter (10163 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10163 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10163 : Reach 10163 100711619339733 164554426052 := by
  have hr := row_10163
  have hl := log_bounds hr.1
    (by change logScale (10163 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10159) (T := 100619354250236) (U := 164538234531)
    (by norm_num) (by norm_num) hr.1 gap_10163
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10159

theorem gap_10169 : PrimeGap 10163 10169 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10169 :
    (10169 : ℕ).Prime ∧ logScale (10169 : ℚ) = 13 ∧
      (92270991524 : ℤ) = ⌊logCenter (10169 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10169 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10169 : Reach 10169 100803890331257 164570609611 := by
  have hr := row_10169
  have hl := log_bounds hr.1
    (by change logScale (10169 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10163) (T := 100711619339733) (U := 164554426052)
    (by norm_num) (by norm_num) hr.1 gap_10169
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10163

theorem gap_10177 : PrimeGap 10169 10177 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10177 :
    (10177 : ℕ).Prime ∧ logScale (10177 : ℚ) = 13 ∧
      (92278855478 : ℤ) = ⌊logCenter (10177 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10177 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10177 : Reach 10177 100896169186735 164586782038 := by
  have hr := row_10177
  have hl := log_bounds hr.1
    (by change logScale (10177 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10169) (T := 100803890331257) (U := 164570609611)
    (by norm_num) (by norm_num) hr.1 gap_10177
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10169

theorem gap_10181 : PrimeGap 10177 10181 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10181 :
    (10181 : ℕ).Prime ∧ logScale (10181 : ℚ) = 13 ∧
      (92282785137 : ℤ) = ⌊logCenter (10181 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10181 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10181 : Reach 10181 100988451971872 164602949699 := by
  have hr := row_10181
  have hl := log_bounds hr.1
    (by change logScale (10181 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10177) (T := 100896169186735) (U := 164586782038)
    (by norm_num) (by norm_num) hr.1 gap_10181
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10177

theorem gap_10193 : PrimeGap 10181 10193 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 61, 2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10193 :
    (10193 : ℕ).Prime ∧ logScale (10193 : ℚ) = 13 ∧
      (92294564857 : ℤ) = ⌊logCenter (10193 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10193 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10193 : Reach 10193 101080746536729 164619099910 := by
  have hr := row_10193
  have hl := log_bounds hr.1
    (by change logScale (10193 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10181) (T := 100988451971872) (U := 164602949699)
    (by norm_num) (by norm_num) hr.1 gap_10193
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10181

#print axioms reach_10193

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
