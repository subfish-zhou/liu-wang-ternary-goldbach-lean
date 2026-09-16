import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0561
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13159 : PrimeGap 13151 13159 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 59, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13159 :
    (13159 : ℕ).Prime ∧ logScale (13159 : ℚ) = 13 ∧
      (94848612107 : ℤ) = ⌊logCenter (13159 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13159 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13159 : Reach 13159 130393404824900 169105341625 := by
  have hr := row_13159
  have hl := log_bounds hr.1
    (by change logScale (13159 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13151) (T := 130298556212793) (U := 169092490698)
    (by norm_num) (by norm_num) hr.1 gap_13159
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13151

theorem gap_13163 : PrimeGap 13159 13163 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13163 :
    (13163 : ℕ).Prime ∧ logScale (13163 : ℚ) = 13 ∧
      (94851651390 : ℤ) = ⌊logCenter (13163 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13163 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13163 : Reach 13163 130488256476290 169118189623 := by
  have hr := row_13163
  have hl := log_bounds hr.1
    (by change logScale (13163 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13159) (T := 130393404824900) (U := 169105341625)
    (by norm_num) (by norm_num) hr.1 gap_13163
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13159

theorem gap_13171 : PrimeGap 13163 13171 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13171 :
    (13171 : ℕ).Prime ∧ logScale (13171 : ℚ) = 13 ∧
      (94857727186 : ℤ) = ⌊logCenter (13171 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13171 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13171 : Reach 13171 130583114203476 169131030792 := by
  have hr := row_13171
  have hl := log_bounds hr.1
    (by change logScale (13171 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13163) (T := 130488256476290) (U := 169118189623)
    (by norm_num) (by norm_num) hr.1 gap_13171
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13163

theorem gap_13177 : PrimeGap 13171 13177 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13177 :
    (13177 : ℕ).Prime ∧ logScale (13177 : ℚ) = 13 ∧
      (94862281611 : ℤ) = ⌊logCenter (13177 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13177 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13177 : Reach 13177 130677976485087 169143867088 := by
  have hr := row_13177
  have hl := log_bounds hr.1
    (by change logScale (13177 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13171) (T := 130583114203476) (U := 169131030792)
    (by norm_num) (by norm_num) hr.1 gap_13177
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13171

theorem gap_13183 : PrimeGap 13177 13183 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13183 :
    (13183 : ℕ).Prime ∧ logScale (13183 : ℚ) = 13 ∧
      (94866833963 : ℤ) = ⌊logCenter (13183 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13183 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13183 : Reach 13183 130772843319050 169156698515 := by
  have hr := row_13183
  have hl := log_bounds hr.1
    (by change logScale (13183 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13177) (T := 130677976485087) (U := 169143867088)
    (by norm_num) (by norm_num) hr.1 gap_13183
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13177

theorem gap_13187 : PrimeGap 13183 13187 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13187 :
    (13187 : ℕ).Prime ∧ logScale (13187 : ℚ) = 13 ∧
      (94869867714 : ℤ) = ⌊logCenter (13187 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13187 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13187 : Reach 13187 130867713186764 169169527023 := by
  have hr := row_13187
  have hl := log_bounds hr.1
    (by change logScale (13187 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13183) (T := 130772843319050) (U := 169156698515)
    (by norm_num) (by norm_num) hr.1 gap_13187
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13183

theorem gap_13217 : PrimeGap 13187 13217 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 79, 2, 5, 2, 3, 2, 67, 2, 43, 2, 3, 2, 5, 2, 47, 2, 3, 2, 11, 2, 73, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13217 :
    (13217 : ℕ).Prime ∧ logScale (13217 : ℚ) = 13 ∧
      (94892591553 : ℤ) = ⌊logCenter (13217 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13217 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13217 : Reach 13217 130962605778317 169182327381 := by
  have hr := row_13217
  have hl := log_bounds hr.1
    (by change logScale (13217 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13187) (T := 130867713186764) (U := 169169527023)
    (by norm_num) (by norm_num) hr.1 gap_13217
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13187

theorem gap_13219 : PrimeGap 13217 13219 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13219 :
    (13219 : ℕ).Prime ∧ logScale (13219 : ℚ) = 13 ∧
      (94894104642 : ℤ) = ⌊logCenter (13219 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13219 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13219 : Reach 13219 131057499882959 169195126771 := by
  have hr := row_13219
  have hl := log_bounds hr.1
    (by change logScale (13219 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13217) (T := 130962605778317) (U := 169182327381)
    (by norm_num) (by norm_num) hr.1 gap_13219
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13217

#print axioms reach_13219

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
