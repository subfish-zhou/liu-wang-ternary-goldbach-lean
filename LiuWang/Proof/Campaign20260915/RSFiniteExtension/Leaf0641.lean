import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0640
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14939 : PrimeGap 14929 14939 :=
  (primeGap_of_factors (ds := [2, 3, 2, 109, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14939 :
    (14939 : ℕ).Prime ∧ logScale (14939 : ℚ) = 13 ∧
      (96117305186 : ℤ) = ⌊logCenter (14939 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14939 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14939 : Reach 14939 147967255445313 171334751541 := by
  have hr := row_14939
  have hl := log_bounds hr.1
    (by change logScale (14939 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14929) (T := 147871138140127) (U := 171323282583)
    (by norm_num) (by norm_num) hr.1 gap_14939
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14929

theorem gap_14947 : PrimeGap 14939 14947 :=
  (primeGap_of_factors (ds := [2, 67, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14947 :
    (14947 : ℕ).Prime ∧ logScale (14947 : ℚ) = 13 ∧
      (96122658864 : ℤ) = ⌊logCenter (14947 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14947 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14947 : Reach 14947 148063378104177 171346215127 := by
  have hr := row_14947
  have hl := log_bounds hr.1
    (by change logScale (14947 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14939) (T := 147967255445313) (U := 171334751541)
    (by norm_num) (by norm_num) hr.1 gap_14947
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14939

theorem gap_14951 : PrimeGap 14947 14951 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14951 :
    (14951 : ℕ).Prime ∧ logScale (14951 : ℚ) = 13 ∧
      (96125334628 : ℤ) = ⌊logCenter (14951 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14951 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14951 : Reach 14951 148159503438805 171357676413 := by
  have hr := row_14951
  have hl := log_bounds hr.1
    (by change logScale (14951 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14947) (T := 148063378104177) (U := 171346215127)
    (by norm_num) (by norm_num) hr.1 gap_14951
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14947

theorem gap_14957 : PrimeGap 14951 14957 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14957 :
    (14957 : ℕ).Prime ∧ logScale (14957 : ℚ) = 13 ∧
      (96129346932 : ℤ) = ⌊logCenter (14957 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14957 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14957 : Reach 14957 148255632785737 171369133867 := by
  have hr := row_14957
  have hl := log_bounds hr.1
    (by change logScale (14957 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14951) (T := 148159503438805) (U := 171357676413)
    (by norm_num) (by norm_num) hr.1 gap_14957
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14951

theorem gap_14969 : PrimeGap 14957 14969 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14969 :
    (14969 : ℕ).Prime ∧ logScale (14969 : ℚ) = 13 ∧
      (96137366715 : ℤ) = ⌊logCenter (14969 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14969 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14969 : Reach 14969 148351770152452 171380582901 := by
  have hr := row_14969
  have hl := log_bounds hr.1
    (by change logScale (14969 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14957) (T := 148255632785737) (U := 171369133867)
    (by norm_num) (by norm_num) hr.1 gap_14969
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14957

theorem gap_14983 : PrimeGap 14969 14983 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 71, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14983 :
    (14983 : ℕ).Prime ∧ logScale (14983 : ℚ) = 13 ∧
      (96146715006 : ℤ) = ⌊logCenter (14983 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14983 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14983 : Reach 14983 148447916867458 171392022001 := by
  have hr := row_14983
  have hl := log_bounds hr.1
    (by change logScale (14983 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14969) (T := 148351770152452) (U := 171380582901)
    (by norm_num) (by norm_num) hr.1 gap_14983
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14969

theorem gap_15013 : PrimeGap 14983 15013 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15013 :
    (15013 : ℕ).Prime ∧ logScale (15013 : ℚ) = 13 ∧
      (96166717680 : ℤ) = ⌊logCenter (15013 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15013 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15013 : Reach 15013 148544083585138 171403439003 := by
  have hr := row_15013
  have hl := log_bounds hr.1
    (by change logScale (15013 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14983) (T := 148447916867458) (U := 171392022001)
    (by norm_num) (by norm_num) hr.1 gap_15013
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14983

theorem gap_15017 : PrimeGap 15013 15017 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15017 :
    (15017 : ℕ).Prime ∧ logScale (15017 : ℚ) = 13 ∧
      (96169381683 : ℤ) = ⌊logCenter (15017 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15017 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15017 : Reach 15017 148640252966821 171414853724 := by
  have hr := row_15017
  have hl := log_bounds hr.1
    (by change logScale (15017 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15013) (T := 148544083585138) (U := 171403439003)
    (by norm_num) (by norm_num) hr.1 gap_15017
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15013

#print axioms reach_15017

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
