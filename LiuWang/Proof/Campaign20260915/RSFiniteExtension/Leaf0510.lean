import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block050
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11927 : PrimeGap 11923 11927 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11927 :
    (11927 : ℕ).Prime ∧ logScale (11927 : ℚ) = 13 ∧
      (93865600131 : ℤ) = ⌊logCenter (11927 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11927 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11927 : Reach 11927 117559824379276 167280049056 := by
  have hr := row_11927
  have hl := log_bounds hr.1
    (by change logScale (11927 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11923) (T := 117465958779145) (U := 167266023731)
    (by norm_num) (by norm_num) hr.1 gap_11927
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11923

theorem gap_11933 : PrimeGap 11927 11933 :=
  (primeGap_of_factors (ds := [2, 79, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11933 :
    (11933 : ℕ).Prime ∧ logScale (11933 : ℚ) = 13 ∧
      (93870629469 : ℤ) = ⌊logCenter (11933 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11933 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11933 : Reach 11933 117653695008745 167294068504 := by
  have hr := row_11933
  have hl := log_bounds hr.1
    (by change logScale (11933 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11927) (T := 117559824379276) (U := 167280049056)
    (by norm_num) (by norm_num) hr.1 gap_11933
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11927

theorem gap_11939 : PrimeGap 11933 11939 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11939 :
    (11939 : ℕ).Prime ∧ logScale (11939 : ℚ) = 13 ∧
      (93875656279 : ℤ) = ⌊logCenter (11939 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11939 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11939 : Reach 11939 117747570665024 167308082080 := by
  have hr := row_11939
  have hl := log_bounds hr.1
    (by change logScale (11939 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11933) (T := 117653695008745) (U := 167294068504)
    (by norm_num) (by norm_num) hr.1 gap_11939
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11933

theorem gap_11941 : PrimeGap 11939 11941 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11941 :
    (11941 : ℕ).Prime ∧ logScale (11941 : ℚ) = 13 ∧
      (93877331321 : ℤ) = ⌊logCenter (11941 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11941 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11941 : Reach 11941 117841447996345 167322094483 := by
  have hr := row_11941
  have hl := log_bounds hr.1
    (by change logScale (11941 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11939) (T := 117747570665024) (U := 167308082080)
    (by norm_num) (by norm_num) hr.1 gap_11941
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11939

theorem gap_11953 : PrimeGap 11941 11953 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11953 :
    (11953 : ℕ).Prime ∧ logScale (11953 : ℚ) = 13 ∧
      (93887375684 : ℤ) = ⌊logCenter (11953 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11953 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11953 : Reach 11953 117935335372029 167336093989 := by
  have hr := row_11953
  have hl := log_bounds hr.1
    (by change logScale (11953 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11941) (T := 117841447996345) (U := 167322094483)
    (by norm_num) (by norm_num) hr.1 gap_11953
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11941

theorem gap_11959 : PrimeGap 11953 11959 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11959 :
    (11959 : ℕ).Prime ∧ logScale (11959 : ℚ) = 13 ∧
      (93892394085 : ℤ) = ⌊logCenter (11959 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11959 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11959 : Reach 11959 118029227766114 167350087642 := by
  have hr := row_11959
  have hl := log_bounds hr.1
    (by change logScale (11959 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11953) (T := 117935335372029) (U := 167336093989)
    (by norm_num) (by norm_num) hr.1 gap_11959
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11953

theorem gap_11969 : PrimeGap 11959 11969 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11969 :
    (11969 : ℕ).Prime ∧ logScale (11969 : ℚ) = 13 ∧
      (93900752494 : ℤ) = ⌊logCenter (11969 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11969 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11969 : Reach 11969 118123128518608 167364070771 := by
  have hr := row_11969
  have hl := log_bounds hr.1
    (by change logScale (11969 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11959) (T := 118029227766114) (U := 167350087642)
    (by norm_num) (by norm_num) hr.1 gap_11969
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11959

theorem gap_11971 : PrimeGap 11969 11971 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11971 :
    (11971 : ℕ).Prime ∧ logScale (11971 : ℚ) = 13 ∧
      (93902423338 : ℤ) = ⌊logCenter (11971 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11971 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11971 : Reach 11971 118217030941946 167378052732 := by
  have hr := row_11971
  have hl := log_bounds hr.1
    (by change logScale (11971 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11969) (T := 118123128518608) (U := 167364070771)
    (by norm_num) (by norm_num) hr.1 gap_11971
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11969

#print axioms reach_11971

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
