import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block037
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8999 : PrimeGap 8971 8999 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 47, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 89, 2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8999 :
    (8999 : ℕ).Prime ∧ logScale (8999 : ℚ) = 13 ∧
      (91048687356 : ℤ) = ⌊logCenter (8999 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8999 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8999 : Reach 8999 88703749894238 162315579807 := by
  have hr := row_8999
  have hl := log_bounds hr.1
    (by change logScale (8999 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8971) (T := 88612701206882) (U := 162297542738)
    (by norm_num) (by norm_num) hr.1 gap_8999
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8971

theorem gap_9001 : PrimeGap 8999 9001 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9001 :
    (9001 : ℕ).Prime ∧ logScale (9001 : ℚ) = 13 ∧
      (91050909578 : ℤ) = ⌊logCenter (9001 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9001 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9001 : Reach 9001 88794800803816 162333614872 := by
  have hr := row_9001
  have hl := log_bounds hr.1
    (by change logScale (9001 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8999) (T := 88703749894238) (U := 162315579807)
    (by norm_num) (by norm_num) hr.1 gap_9001
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8999

theorem gap_9007 : PrimeGap 9001 9007 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9007 :
    (9007 : ℕ).Prime ∧ logScale (9007 : ℚ) = 13 ∧
      (91057573284 : ℤ) = ⌊logCenter (9007 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9007 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9007 : Reach 9007 88885858377100 162351639924 := by
  have hr := row_9007
  have hl := log_bounds hr.1
    (by change logScale (9007 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9001) (T := 88794800803816) (U := 162333614872)
    (by norm_num) (by norm_num) hr.1 gap_9007
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9001

theorem gap_9011 : PrimeGap 9007 9011 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9011 :
    (9011 : ℕ).Prime ∧ logScale (9011 : ℚ) = 13 ∧
      (91062013288 : ℤ) = ⌊logCenter (9011 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9011 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9011 : Reach 9011 88976920390388 162369658974 := by
  have hr := row_9011
  have hl := log_bounds hr.1
    (by change logScale (9011 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9007) (T := 88885858377100) (U := 162351639924)
    (by norm_num) (by norm_num) hr.1 gap_9011
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9007

theorem gap_9013 : PrimeGap 9011 9013 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9013 :
    (9013 : ℕ).Prime ∧ logScale (9013 : ℚ) = 13 ∧
      (91064232551 : ℤ) = ⌊logCenter (9013 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9013 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9013 : Reach 9013 89067984622939 162387676025 := by
  have hr := row_9013
  have hl := log_bounds hr.1
    (by change logScale (9013 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9011) (T := 88976920390388) (U := 162369658974)
    (by norm_num) (by norm_num) hr.1 gap_9013
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9011

theorem gap_9029 : PrimeGap 9013 9029 :=
  (primeGap_of_factors (ds := [2, 3, 2, 71, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9029 :
    (9029 : ℕ).Prime ∧ logScale (9029 : ℚ) = 13 ∧
      (91081968949 : ℤ) = ⌊logCenter (9029 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9029 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9029 : Reach 9029 89159066591888 162405663141 := by
  have hr := row_9029
  have hl := log_bounds hr.1
    (by change logScale (9029 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9013) (T := 89067984622939) (U := 162387676025)
    (by norm_num) (by norm_num) hr.1 gap_9029
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9013

theorem gap_9041 : PrimeGap 9029 9041 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9041 :
    (9041 : ℕ).Prime ∧ logScale (9041 : ℚ) = 13 ∧
      (91095250633 : ℤ) = ⌊logCenter (9041 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9041 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9041 : Reach 9041 89250161842521 162423628370 := by
  have hr := row_9041
  have hl := log_bounds hr.1
    (by change logScale (9041 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9029) (T := 89159066591888) (U := 162405663141)
    (by norm_num) (by norm_num) hr.1 gap_9041
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9029

theorem gap_9043 : PrimeGap 9041 9043 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9043 :
    (9043 : ℕ).Prime ∧ logScale (9043 : ℚ) = 13 ∧
      (91097462533 : ℤ) = ⌊logCenter (9043 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9043 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9043 : Reach 9043 89341259305054 162441591612 := by
  have hr := row_9043
  have hl := log_bounds hr.1
    (by change logScale (9043 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9041) (T := 89250161842521) (U := 162423628370)
    (by norm_num) (by norm_num) hr.1 gap_9043
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9041

#print axioms reach_9043

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
