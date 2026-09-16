import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0470
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11069 : PrimeGap 11059 11069 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11069 :
    (11069 : ℕ).Prime ∧ logScale (11069 : ℚ) = 13 ∧
      (93119036840 : ℤ) = ⌊logCenter (11069 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11069 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11069 : Reach 11069 109331992885088 166004133896 := by
  have hr := row_11069
  have hl := log_bounds hr.1
    (by change logScale (11069 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11059) (T := 109238873848248) (U := 165989136684)
    (by norm_num) (by norm_num) hr.1 gap_11069
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11059

theorem gap_11071 : PrimeGap 11069 11071 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11071 :
    (11071 : ℕ).Prime ∧ logScale (11071 : ℚ) = 13 ∧
      (93120843524 : ℤ) = ⌊logCenter (11071 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11071 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11071 : Reach 11071 109425113728612 166019129753 := by
  have hr := row_11071
  have hl := log_bounds hr.1
    (by change logScale (11071 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11069) (T := 109331992885088) (U := 166004133896)
    (by norm_num) (by norm_num) hr.1 gap_11071
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11069

theorem gap_11083 : PrimeGap 11071 11083 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11083 :
    (11083 : ℕ).Prime ∧ logScale (11083 : ℚ) = 13 ∧
      (93131676783 : ℤ) = ⌊logCenter (11083 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11083 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11083 : Reach 11083 109518245405395 166034110725 := by
  have hr := row_11083
  have hl := log_bounds hr.1
    (by change logScale (11083 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11071) (T := 109425113728612) (U := 166019129753)
    (by norm_num) (by norm_num) hr.1 gap_11083
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11071

theorem gap_11087 : PrimeGap 11083 11087 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11087 :
    (11087 : ℕ).Prime ∧ logScale (11087 : ℚ) = 13 ∧
      (93135285263 : ℤ) = ⌊logCenter (11087 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11087 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11087 : Reach 11087 109611380690658 166049087643 := by
  have hr := row_11087
  have hl := log_bounds hr.1
    (by change logScale (11087 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11083) (T := 109518245405395) (U := 166034110725)
    (by norm_num) (by norm_num) hr.1 gap_11087
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11083

theorem gap_11093 : PrimeGap 11087 11093 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11093 :
    (11093 : ℕ).Prime ∧ logScale (11093 : ℚ) = 13 ∧
      (93140695543 : ℤ) = ⌊logCenter (11093 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11093 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11093 : Reach 11093 109704521386201 166064057810 := by
  have hr := row_11093
  have hl := log_bounds hr.1
    (by change logScale (11093 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11087) (T := 109611380690658) (U := 166049087643)
    (by norm_num) (by norm_num) hr.1 gap_11093
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11087

theorem gap_11113 : PrimeGap 11093 11113 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 29, 2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11113 :
    (11113 : ℕ).Prime ∧ logScale (11113 : ℚ) = 13 ∧
      (93158708698 : ℤ) = ⌊logCenter (11113 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11113 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11113 : Reach 11113 109797680094899 166079002380 := by
  have hr := row_11113
  have hl := log_bounds hr.1
    (by change logScale (11113 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11093) (T := 109704521386201) (U := 166064057810)
    (by norm_num) (by norm_num) hr.1 gap_11113
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11093

theorem gap_11117 : PrimeGap 11113 11117 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11117 :
    (11117 : ℕ).Prime ∧ logScale (11117 : ℚ) = 13 ∧
      (93162307438 : ℤ) = ⌊logCenter (11117 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11117 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11117 : Reach 11117 109890842402337 166093942917 := by
  have hr := row_11117
  have hl := log_bounds hr.1
    (by change logScale (11117 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11113) (T := 109797680094899) (U := 166079002380)
    (by norm_num) (by norm_num) hr.1 gap_11117
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11113

theorem gap_11119 : PrimeGap 11117 11119 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11119 :
    (11119 : ℕ).Prime ∧ logScale (11119 : ℚ) = 13 ∧
      (93164106323 : ℤ) = ⌊logCenter (11119 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11119 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11119 : Reach 11119 109984006508660 166108882110 := by
  have hr := row_11119
  have hl := log_bounds hr.1
    (by change logScale (11119 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11117) (T := 109890842402337) (U := 166093942917)
    (by norm_num) (by norm_num) hr.1 gap_11119
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11117

#print axioms reach_11119

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
