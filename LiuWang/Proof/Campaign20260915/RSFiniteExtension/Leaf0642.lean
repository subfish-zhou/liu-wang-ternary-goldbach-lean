import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0641
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15031 : PrimeGap 15017 15031 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 83, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15031 :
    (15031 : ℕ).Prime ∧ logScale (15031 : ℚ) = 13 ∧
      (96178700107 : ℤ) = ⌊logCenter (15031 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15031 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15031 : Reach 15031 148736431666928 171426258572 := by
  have hr := row_15031
  have hl := log_bounds hr.1
    (by change logScale (15031 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15017) (T := 148640252966821) (U := 171414853724)
    (by norm_num) (by norm_num) hr.1 gap_15031
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15017

theorem gap_15053 : PrimeGap 15031 15053 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3, 2, 41, 2, 101, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15053 :
    (15053 : ℕ).Prime ∧ logScale (15053 : ℚ) = 13 ∧
      (96193325824 : ℤ) = ⌊logCenter (15053 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15053 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15053 : Reach 15053 148832624992752 171437647508 := by
  have hr := row_15053
  have hl := log_bounds hr.1
    (by change logScale (15053 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15031) (T := 148736431666928) (U := 171426258572)
    (by norm_num) (by norm_num) hr.1 gap_15053
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15031

theorem gap_15061 : PrimeGap 15053 15061 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15061 :
    (15061 : ℕ).Prime ∧ logScale (15061 : ℚ) = 13 ∧
      (96198638968 : ℤ) = ⌊logCenter (15061 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15061 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15061 : Reach 15061 148928823631720 171449031150 := by
  have hr := row_15061
  have hl := log_bounds hr.1
    (by change logScale (15061 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15053) (T := 148832624992752) (U := 171437647508)
    (by norm_num) (by norm_num) hr.1 gap_15061
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15053

theorem gap_15073 : PrimeGap 15061 15073 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15073 :
    (15073 : ℕ).Prime ∧ logScale (15073 : ℚ) = 13 ∧
      (96206603394 : ℤ) = ⌊logCenter (15073 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15073 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15073 : Reach 15073 149025030235114 171460406484 := by
  have hr := row_15073
  have hl := log_bounds hr.1
    (by change logScale (15073 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15061) (T := 148928823631720) (U := 171449031150)
    (by norm_num) (by norm_num) hr.1 gap_15073
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15061

theorem gap_15077 : PrimeGap 15073 15077 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15077 :
    (15077 : ℕ).Prime ∧ logScale (15077 : ℚ) = 13 ∧
      (96209256793 : ℤ) = ⌊logCenter (15077 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15077 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15077 : Reach 15077 149121239491907 171471779555 := by
  have hr := row_15077
  have hl := log_bounds hr.1
    (by change logScale (15077 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15073) (T := 149025030235114) (U := 171460406484)
    (by norm_num) (by norm_num) hr.1 gap_15077
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15073

theorem gap_15083 : PrimeGap 15077 15083 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15083 :
    (15083 : ℕ).Prime ∧ logScale (15083 : ℚ) = 13 ∧
      (96213235573 : ℤ) = ⌊logCenter (15083 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15083 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15083 : Reach 15083 149217452727480 171483148855 := by
  have hr := row_15083
  have hl := log_bounds hr.1
    (by change logScale (15083 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15077) (T := 149121239491907) (U := 171471779555)
    (by norm_num) (by norm_num) hr.1 gap_15083
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15077

theorem gap_15091 : PrimeGap 15083 15091 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 79, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15091 :
    (15091 : ℕ).Prime ∧ logScale (15091 : ℚ) = 13 ∧
      (96218538152 : ℤ) = ⌊logCenter (15091 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15091 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15091 : Reach 15091 149313671265632 171494512881 := by
  have hr := row_15091
  have hl := log_bounds hr.1
    (by change logScale (15091 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15083) (T := 149217452727480) (U := 171483148855)
    (by norm_num) (by norm_num) hr.1 gap_15091
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15083

theorem gap_15101 : PrimeGap 15091 15101 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15101 :
    (15101 : ℕ).Prime ∧ logScale (15101 : ℚ) = 13 ∧
      (96225162423 : ℤ) = ⌊logCenter (15101 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15101 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15101 : Reach 15101 149409896428055 171505870134 := by
  have hr := row_15101
  have hl := log_bounds hr.1
    (by change logScale (15101 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15091) (T := 149313671265632) (U := 171494512881)
    (by norm_num) (by norm_num) hr.1 gap_15101
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15091

#print axioms reach_15101

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
