import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0600
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14009 : PrimeGap 13999 14009 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14009 :
    (14009 : ℕ).Prime ∧ logScale (14009 : ℚ) = 13 ∧
      (95474552558 : ℤ) = ⌊logCenter (14009 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14009 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14009 : Reach 14009 138768399778786 170204184908 := by
  have hr := row_14009
  have hl := log_bounds hr.1
    (by change logScale (14009 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13999) (T := 138672925226228) (U := 170192035276)
    (by norm_num) (by norm_num) hr.1 gap_14009
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13999

theorem gap_14011 : PrimeGap 14009 14011 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14011 :
    (14011 : ℕ).Prime ∧ logScale (14011 : ℚ) = 13 ∧
      (95475980109 : ℤ) = ⌊logCenter (14011 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14011 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14011 : Reach 14011 138863875758895 170216333673 := by
  have hr := row_14011
  have hl := log_bounds hr.1
    (by change logScale (14011 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14009) (T := 138768399778786) (U := 170204184908)
    (by norm_num) (by norm_num) hr.1 gap_14011
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14009

theorem gap_14029 : PrimeGap 14011 14029 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 107, 2, 3, 2, 7, 2, 37, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14029 :
    (14029 : ℕ).Prime ∧ logScale (14029 : ℚ) = 13 ∧
      (95488818913 : ℤ) = ⌊logCenter (14029 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14029 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14029 : Reach 14029 138959364577808 170228467715 := by
  have hr := row_14029
  have hl := log_bounds hr.1
    (by change logScale (14029 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14011) (T := 138863875758895) (U := 170216333673)
    (by norm_num) (by norm_num) hr.1 gap_14029
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14011

theorem gap_14033 : PrimeGap 14029 14033 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14033 :
    (14033 : ℕ).Prime ∧ logScale (14033 : ℚ) = 13 ∧
      (95491669743 : ℤ) = ⌊logCenter (14033 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14033 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14033 : Reach 14033 139054856247551 170240599163 := by
  have hr := row_14033
  have hl := log_bounds hr.1
    (by change logScale (14033 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14029) (T := 138959364577808) (U := 170228467715)
    (by norm_num) (by norm_num) hr.1 gap_14033
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14029

theorem gap_14051 : PrimeGap 14033 14051 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 101, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14051 :
    (14051 : ℕ).Prime ∧ logScale (14051 : ℚ) = 13 ∧
      (95504488432 : ℤ) = ⌊logCenter (14051 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14051 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14051 : Reach 14051 139150360735983 170252715932 := by
  have hr := row_14051
  have hl := log_bounds hr.1
    (by change logScale (14051 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14033) (T := 139054856247551) (U := 170240599163)
    (by norm_num) (by norm_num) hr.1 gap_14051
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14033

theorem gap_14057 : PrimeGap 14051 14057 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14057 :
    (14057 : ℕ).Prime ∧ logScale (14057 : ℚ) = 13 ∧
      (95508757679 : ℤ) = ⌊logCenter (14057 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14057 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14057 : Reach 14057 139245869493662 170264828391 := by
  have hr := row_14057
  have hl := log_bounds hr.1
    (by change logScale (14057 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14051) (T := 139150360735983) (U := 170252715932)
    (by norm_num) (by norm_num) hr.1 gap_14057
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14051

theorem gap_14071 : PrimeGap 14057 14071 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14071 :
    (14071 : ℕ).Prime ∧ logScale (14071 : ℚ) = 13 ∧
      (95518712174 : ℤ) = ⌊logCenter (14071 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14071 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14071 : Reach 14071 139341388205836 170276929659 := by
  have hr := row_14071
  have hl := log_bounds hr.1
    (by change logScale (14071 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14057) (T := 139245869493662) (U := 170264828391)
    (by norm_num) (by norm_num) hr.1 gap_14071
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14057

theorem gap_14081 : PrimeGap 14071 14081 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14081 :
    (14081 : ℕ).Prime ∧ logScale (14081 : ℚ) = 13 ∧
      (95525816465 : ℤ) = ⌊logCenter (14081 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14081 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14081 : Reach 14081 139436914022301 170289023191 := by
  have hr := row_14081
  have hl := log_bounds hr.1
    (by change logScale (14081 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14071) (T := 139341388205836) (U := 170276929659)
    (by norm_num) (by norm_num) hr.1 gap_14081
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14071

#print axioms reach_14081

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
