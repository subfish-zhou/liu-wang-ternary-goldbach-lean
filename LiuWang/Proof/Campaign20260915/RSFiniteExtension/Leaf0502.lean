import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0501
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11839 : PrimeGap 11833 11839 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11839 :
    (11839 : ℕ).Prime ∧ logScale (11839 : ℚ) = 13 ∧
      (93791544420 : ℤ) = ⌊logCenter (11839 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11839 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11839 : Reach 11839 116809101194071 167167596216 := by
  have hr := row_11839
  have hl := log_bounds hr.1
    (by change logScale (11839 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11833) (T := 116715309649651) (U := 167153476138)
    (by norm_num) (by norm_num) hr.1 gap_11839
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11833

theorem gap_11863 : PrimeGap 11839 11863 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 71, 2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11863 :
    (11863 : ℕ).Prime ∧ logScale (11863 : ℚ) = 13 ∧
      (93811795882 : ℤ) = ⌊logCenter (11863 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11863 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11863 : Reach 11863 116902912989953 167181688916 := by
  have hr := row_11863
  have hl := log_bounds hr.1
    (by change logScale (11863 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11839) (T := 116809101194071) (U := 167167596216)
    (by norm_num) (by norm_num) hr.1 gap_11863
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11839

theorem gap_11867 : PrimeGap 11863 11867 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11867 :
    (11867 : ℕ).Prime ∧ logScale (11867 : ℚ) = 13 ∧
      (93815167142 : ℤ) = ⌊logCenter (11867 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11867 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11867 : Reach 11867 116996728157095 167195778053 := by
  have hr := row_11867
  have hl := log_bounds hr.1
    (by change logScale (11867 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11863) (T := 116902912989953) (U := 167181688916)
    (by norm_num) (by norm_num) hr.1 gap_11867
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11863

theorem gap_11887 : PrimeGap 11867 11887 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 109, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11887 :
    (11887 : ℕ).Prime ∧ logScale (11887 : ℚ) = 13 ∧
      (93832006416 : ℤ) = ⌊logCenter (11887 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11887 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11887 : Reach 11887 117090560163511 167209844668 := by
  have hr := row_11887
  have hl := log_bounds hr.1
    (by change logScale (11887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11867) (T := 116996728157095) (U := 167195778053)
    (by norm_num) (by norm_num) hr.1 gap_11887
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11867

theorem gap_11897 : PrimeGap 11887 11897 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11897 :
    (11897 : ℕ).Prime ∧ logScale (11897 : ℚ) = 13 ∧
      (93840415430 : ℤ) = ⌊logCenter (11897 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11897 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11897 : Reach 11897 117184400578941 167223900641 := by
  have hr := row_11897
  have hl := log_bounds hr.1
    (by change logScale (11897 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11887) (T := 117090560163511) (U := 167209844668)
    (by norm_num) (by norm_num) hr.1 gap_11897
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11887

theorem gap_11903 : PrimeGap 11897 11903 :=
  (primeGap_of_factors (ds := [2, 73, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11903 :
    (11903 : ℕ).Prime ∧ logScale (11903 : ℚ) = 13 ∧
      (93845457447 : ℤ) = ⌊logCenter (11903 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11903 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11903 : Reach 11903 117278246036388 167237950709 := by
  have hr := row_11903
  have hl := log_bounds hr.1
    (by change logScale (11903 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11897) (T := 117184400578941) (U := 167223900641)
    (by norm_num) (by norm_num) hr.1 gap_11903
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11897

theorem gap_11909 : PrimeGap 11903 11909 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11909 :
    (11909 : ℕ).Prime ∧ logScale (11909 : ℚ) = 13 ∧
      (93850496923 : ℤ) = ⌊logCenter (11909 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11909 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11909 : Reach 11909 117372096533311 167251994877 := by
  have hr := row_11909
  have hl := log_bounds hr.1
    (by change logScale (11909 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11903) (T := 117278246036388) (U := 167237950709)
    (by norm_num) (by norm_num) hr.1 gap_11909
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11903

theorem gap_11923 : PrimeGap 11909 11923 :=
  (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11923 :
    (11923 : ℕ).Prime ∧ logScale (11923 : ℚ) = 13 ∧
      (93862245834 : ℤ) = ⌊logCenter (11923 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11923 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11923 : Reach 11923 117465958779145 167266023731 := by
  have hr := row_11923
  have hl := log_bounds hr.1
    (by change logScale (11923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11909) (T := 117372096533311) (U := 167251994877)
    (by norm_num) (by norm_num) hr.1 gap_11923
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11909

#print axioms reach_11923

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
