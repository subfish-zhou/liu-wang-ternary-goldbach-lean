import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block064
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15107 : PrimeGap 15101 15107 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15107 :
    (15107 : ℕ).Prime ∧ logScale (15107 : ℚ) = 13 ∧
      (96229134881 : ℤ) = ⌊logCenter (15107 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15107 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15107 : Reach 15107 149506125562936 171517223628 := by
  have hr := row_15107
  have hl := log_bounds hr.1
    (by change logScale (15107 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15101) (T := 149409896428055) (U := 171505870134)
    (by norm_num) (by norm_num) hr.1 gap_15107
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15101

theorem gap_15121 : PrimeGap 15107 15121 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15121 :
    (15121 : ℕ).Prime ∧ logScale (15121 : ℚ) = 13 ∧
      (96238397817 : ℤ) = ⌊logCenter (15121 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15121 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15121 : Reach 15121 149602363960753 171528567360 := by
  have hr := row_15121
  have hl := log_bounds hr.1
    (by change logScale (15121 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15107) (T := 149506125562936) (U := 171517223628)
    (by norm_num) (by norm_num) hr.1 gap_15121
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15107

theorem gap_15131 : PrimeGap 15121 15131 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15131 :
    (15131 : ℕ).Prime ∧ logScale (15131 : ℚ) = 13 ∧
      (96245008950 : ℤ) = ⌊logCenter (15131 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15131 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15131 : Reach 15131 149698608969703 171539904344 := by
  have hr := row_15131
  have hl := log_bounds hr.1
    (by change logScale (15131 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15121) (T := 149602363960753) (U := 171528567360)
    (by norm_num) (by norm_num) hr.1 gap_15131
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15121

theorem gap_15137 : PrimeGap 15131 15137 :=
  (primeGap_of_factors (ds := [2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15137 :
    (15137 : ℕ).Prime ∧ logScale (15137 : ℚ) = 13 ∧
      (96248973533 : ℤ) = ⌊logCenter (15137 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15137 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15137 : Reach 15137 149794857943236 171551237583 := by
  have hr := row_15137
  have hl := log_bounds hr.1
    (by change logScale (15137 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15131) (T := 149698608969703) (U := 171539904344)
    (by norm_num) (by norm_num) hr.1 gap_15137
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15131

theorem gap_15139 : PrimeGap 15137 15139 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15139 :
    (15139 : ℕ).Prime ∧ logScale (15139 : ℚ) = 13 ∧
      (96250294712 : ℤ) = ⌊logCenter (15139 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15139 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15139 : Reach 15139 149891108237948 171562570074 := by
  have hr := row_15139
  have hl := log_bounds hr.1
    (by change logScale (15139 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15137) (T := 149794857943236) (U := 171551237583)
    (by norm_num) (by norm_num) hr.1 gap_15139
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15137

theorem gap_15149 : PrimeGap 15139 15149 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15149 :
    (15149 : ℕ).Prime ∧ logScale (15149 : ℚ) = 13 ∧
      (96256897987 : ℤ) = ⌊logCenter (15149 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15149 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15149 : Reach 15149 149987365135935 171573895832 := by
  have hr := row_15149
  have hl := log_bounds hr.1
    (by change logScale (15149 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15139) (T := 149891108237948) (U := 171562570074)
    (by norm_num) (by norm_num) hr.1 gap_15149
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15139

theorem gap_15161 : PrimeGap 15149 15161 :=
  (primeGap_of_factors (ds := [2, 109, 2, 3, 2, 5, 2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15161 :
    (15161 : ℕ).Prime ∧ logScale (15161 : ℚ) = 13 ∧
      (96264816167 : ℤ) = ⌊logCenter (15161 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15161 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15161 : Reach 15161 150083629952102 171585213372 := by
  have hr := row_15161
  have hl := log_bounds hr.1
    (by change logScale (15161 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15149) (T := 149987365135935) (U := 171573895832)
    (by norm_num) (by norm_num) hr.1 gap_15161
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15149

theorem gap_15173 : PrimeGap 15161 15173 :=
  (primeGap_of_factors (ds := [2, 59, 2, 3, 2, 29, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15173 :
    (15173 : ℕ).Prime ∧ logScale (15173 : ℚ) = 13 ∧
      (96272728081 : ℤ) = ⌊logCenter (15173 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15173 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15173 : Reach 15173 150179902680183 171596522706 := by
  have hr := row_15173
  have hl := log_bounds hr.1
    (by change logScale (15173 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15161) (T := 150083629952102) (U := 171585213372)
    (by norm_num) (by norm_num) hr.1 gap_15173
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15161

#print axioms reach_15173

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
