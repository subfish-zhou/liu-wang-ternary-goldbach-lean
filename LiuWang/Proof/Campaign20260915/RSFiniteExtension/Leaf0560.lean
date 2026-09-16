import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block055
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13003 : PrimeGap 13001 13003 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13003 :
    (13003 : ℕ).Prime ∧ logScale (13003 : ℚ) = 13 ∧
      (94729353756 : ℤ) = ⌊logCenter (13003 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13003 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13003 : Reach 13003 128876738096431 168898669697 := by
  have hr := row_13003
  have hl := log_bounds hr.1
    (by change logScale (13003 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13001) (T := 128782008742675) (U := 168885680489)
    (by norm_num) (by norm_num) hr.1 gap_13003
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13001

theorem gap_13007 : PrimeGap 13003 13007 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13007 :
    (13007 : ℕ).Prime ∧ logScale (13007 : ℚ) = 13 ∧
      (94732429496 : ℤ) = ⌊logCenter (13007 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13007 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13007 : Reach 13007 128971470525927 168911655909 := by
  have hr := row_13007
  have hl := log_bounds hr.1
    (by change logScale (13007 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13003) (T := 128876738096431) (U := 168898669697)
    (by norm_num) (by norm_num) hr.1 gap_13007
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13003

theorem gap_13009 : PrimeGap 13007 13009 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13009 :
    (13009 : ℕ).Prime ∧ logScale (13009 : ℚ) = 13 ∧
      (94733967012 : ℤ) = ⌊logCenter (13009 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13009 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13009 : Reach 13009 129066204492939 168924641123 := by
  have hr := row_13009
  have hl := log_bounds hr.1
    (by change logScale (13009 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13007) (T := 128971470525927) (U := 168911655909)
    (by norm_num) (by norm_num) hr.1 gap_13009
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13007

theorem gap_13033 : PrimeGap 13009 13033 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 83, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13033 :
    (13033 : ℕ).Prime ∧ logScale (13033 : ℚ) = 13 ∧
      (94752398781 : ℤ) = ⌊logCenter (13033 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13033 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13033 : Reach 13033 129160956891720 168937603419 := by
  have hr := row_13033
  have hl := log_bounds hr.1
    (by change logScale (13033 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13009) (T := 129066204492939) (U := 168924641123)
    (by norm_num) (by norm_num) hr.1 gap_13033
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13009

theorem gap_13037 : PrimeGap 13033 13037 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13037 :
    (13037 : ℕ).Prime ∧ logScale (13037 : ℚ) = 13 ∧
      (94755467442 : ℤ) = ⌊logCenter (13037 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13037 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13037 : Reach 13037 129255712359162 168950562732 := by
  have hr := row_13037
  have hl := log_bounds hr.1
    (by change logScale (13037 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13033) (T := 129160956891720) (U := 168937603419)
    (by norm_num) (by norm_num) hr.1 gap_13037
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13033

theorem gap_13043 : PrimeGap 13037 13043 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13043 :
    (13043 : ℕ).Prime ∧ logScale (13043 : ℚ) = 13 ∧
      (94760068669 : ℤ) = ⌊logCenter (13043 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13043 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13043 : Reach 13043 129350472427831 168963517077 := by
  have hr := row_13043
  have hl := log_bounds hr.1
    (by change logScale (13043 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13037) (T := 129255712359162) (U := 168950562732)
    (by norm_num) (by norm_num) hr.1 gap_13043
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13037

theorem gap_13049 : PrimeGap 13043 13049 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13049 :
    (13049 : ℕ).Prime ∧ logScale (13049 : ℚ) = 13 ∧
      (94764667780 : ℤ) = ⌊logCenter (13049 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13049 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13049 : Reach 13049 129445237095611 168976466458 := by
  have hr := row_13049
  have hl := log_bounds hr.1
    (by change logScale (13049 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13043) (T := 129350472427831) (U := 168963517077)
    (by norm_num) (by norm_num) hr.1 gap_13049
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13043

theorem gap_13063 : PrimeGap 13049 13063 :=
  (primeGap_of_factors (ds := [2, 31, 2, 3, 2, 5, 2, 11, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13063 :
    (13063 : ℕ).Prime ∧ logScale (13063 : ℚ) = 13 ∧
      (94775390821 : ℤ) = ⌊logCenter (13063 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13063 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13063 : Reach 13063 129540012486432 168989402951 := by
  have hr := row_13063
  have hl := log_bounds hr.1
    (by change logScale (13063 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13049) (T := 129445237095611) (U := 168976466458)
    (by norm_num) (by norm_num) hr.1 gap_13063
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13049

#print axioms reach_13063

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
