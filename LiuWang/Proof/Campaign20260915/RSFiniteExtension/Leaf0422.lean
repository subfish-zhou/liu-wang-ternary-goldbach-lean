import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0421
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9973 : PrimeGap 9967 9973 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9973 :
    (9973 : ℕ).Prime ∧ logScale (9973 : ℚ) = 13 ∧
      (92076367170 : ℤ) = ⌊logCenter (9973 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9973 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9973 : Reach 9973 98959913755389 164244897059 := by
  have hr := row_9973
  have hl := log_bounds hr.1
    (by change logScale (9973 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9967) (T := 98867837388219) (U := 164228428103)
    (by norm_num) (by norm_num) hr.1 gap_9973
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9967

theorem gap_10007 : PrimeGap 9973 10007 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 17, 2, 3, 2, 67, 2, 5, 2, 3, 2, 7, 2, 97, 2, 3, 2, 5, 2, 13, 2, 3, 2, 73, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10007 :
    (10007 : ℕ).Prime ∧ logScale (10007 : ℚ) = 13 ∧
      (92110401237 : ℤ) = ⌊logCenter (10007 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10007 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10007 : Reach 10007 99052024156626 164261311700 := by
  have hr := row_10007
  have hl := log_bounds hr.1
    (by change logScale (10007 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9973) (T := 98959913755389) (U := 164244897059)
    (by norm_num) (by norm_num) hr.1 gap_10007
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9973

theorem gap_10009 : PrimeGap 10007 10009 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10009 :
    (10009 : ℕ).Prime ∧ logScale (10009 : ℚ) = 13 ∧
      (92112399638 : ℤ) = ⌊logCenter (10009 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10009 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10009 : Reach 10009 99144136556264 164277724701 := by
  have hr := row_10009
  have hl := log_bounds hr.1
    (by change logScale (10009 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10007) (T := 99052024156626) (U := 164261311700)
    (by norm_num) (by norm_num) hr.1 gap_10009
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10007

theorem gap_10037 : PrimeGap 10009 10037 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 5, 2, 3, 2, 43, 2, 11, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 79, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10037 :
    (10037 : ℕ).Prime ∧ logScale (10037 : ℚ) = 13 ∧
      (92140335404 : ℤ) = ⌊logCenter (10037 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10037 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10037 : Reach 10037 99236276891668 164294093546 := by
  have hr := row_10037
  have hl := log_bounds hr.1
    (by change logScale (10037 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10009) (T := 99144136556264) (U := 164277724701)
    (by norm_num) (by norm_num) hr.1 gap_10037
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10009

theorem gap_10039 : PrimeGap 10037 10039 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10039 :
    (10039 : ℕ).Prime ∧ logScale (10039 : ℚ) = 13 ∧
      (92142327833 : ℤ) = ⌊logCenter (10039 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10039 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10039 : Reach 10039 99328419219501 164310460760 := by
  have hr := row_10039
  have hl := log_bounds hr.1
    (by change logScale (10039 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10037) (T := 99236276891668) (U := 164294093546)
    (by norm_num) (by norm_num) hr.1 gap_10039
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10037

theorem gap_10061 : PrimeGap 10039 10061 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 89, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10061 :
    (10061 : ℕ).Prime ∧ logScale (10061 : ℚ) = 13 ∧
      (92164218389 : ℤ) = ⌊logCenter (10061 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10061 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10061 : Reach 10061 99420583437890 164326793808 := by
  have hr := row_10061
  have hl := log_bounds hr.1
    (by change logScale (10061 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10039) (T := 99328419219501) (U := 164310460760)
    (by norm_num) (by norm_num) hr.1 gap_10061
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10039

theorem gap_10067 : PrimeGap 10061 10067 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10067 :
    (10067 : ℕ).Prime ∧ logScale (10067 : ℚ) = 13 ∧
      (92170180233 : ℤ) = ⌊logCenter (10067 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10067 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10067 : Reach 10067 99512753618123 164343118743 := by
  have hr := row_10067
  have hl := log_bounds hr.1
    (by change logScale (10067 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10061) (T := 99420583437890) (U := 164326793808)
    (by norm_num) (by norm_num) hr.1 gap_10067
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10061

theorem gap_10069 : PrimeGap 10067 10069 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10069 :
    (10069 : ℕ).Prime ∧ logScale (10069 : ℚ) = 13 ∧
      (92172166725 : ℤ) = ⌊logCenter (10069 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10069 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10069 : Reach 10069 99604925784848 164359442057 := by
  have hr := row_10069
  have hl := log_bounds hr.1
    (by change logScale (10069 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10067) (T := 99512753618123) (U := 164343118743)
    (by norm_num) (by norm_num) hr.1 gap_10069
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10067

#print axioms reach_10069

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
