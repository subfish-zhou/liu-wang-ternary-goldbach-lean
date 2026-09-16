import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0371
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8923 : PrimeGap 8893 8923 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 59, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8923 :
    (8923 : ℕ).Prime ∧ logScale (8923 : ℚ) = 13 ∧
      (90963874885 : ℤ) = ⌊logCenter (8923 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8923 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8923 : Reach 8923 87975734880384 162170662420 := by
  have hr := row_8923
  have hl := log_bounds hr.1
    (by change logScale (8923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8893) (T := 87884771005499) (U := 162152487964)
    (by norm_num) (by norm_num) hr.1 gap_8923
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8893

theorem gap_8929 : PrimeGap 8923 8929 :=
  (primeGap_of_factors (ds := [2, 3, 2, 79, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8929 :
    (8929 : ℕ).Prime ∧ logScale (8929 : ℚ) = 13 ∧
      (90970596821 : ℤ) = ⌊logCenter (8929 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8929 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8929 : Reach 8929 88066705477205 162188826697 := by
  have hr := row_8929
  have hl := log_bounds hr.1
    (by change logScale (8929 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8923) (T := 87975734880384) (U := 162170662420)
    (by norm_num) (by norm_num) hr.1 gap_8929
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8923

theorem gap_8933 : PrimeGap 8929 8933 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8933 :
    (8933 : ℕ).Prime ∧ logScale (8933 : ℚ) = 13 ∧
      (90975075603 : ℤ) = ⌊logCenter (8933 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8933 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8933 : Reach 8933 88157680552808 162206984873 := by
  have hr := row_8933
  have hl := log_bounds hr.1
    (by change logScale (8933 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8929) (T := 88066705477205) (U := 162188826697)
    (by norm_num) (by norm_num) hr.1 gap_8933
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8929

theorem gap_8941 : PrimeGap 8933 8941 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8941 :
    (8941 : ℕ).Prime ∧ logScale (8941 : ℚ) = 13 ∧
      (90984027153 : ℤ) = ⌊logCenter (8941 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8941 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8941 : Reach 8941 88248664579961 162225128832 := by
  have hr := row_8941
  have hl := log_bounds hr.1
    (by change logScale (8941 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8933) (T := 88157680552808) (U := 162206984873)
    (by norm_num) (by norm_num) hr.1 gap_8941
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8933

theorem gap_8951 : PrimeGap 8941 8951 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8951 :
    (8951 : ℕ).Prime ∧ logScale (8951 : ℚ) = 13 ∧
      (90995205334 : ℤ) = ⌊logCenter (8951 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8951 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8951 : Reach 8951 88339659785295 162243254545 := by
  have hr := row_8951
  have hl := log_bounds hr.1
    (by change logScale (8951 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8941) (T := 88248664579961) (U := 162225128832)
    (by norm_num) (by norm_num) hr.1 gap_8951
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8941

theorem gap_8963 : PrimeGap 8951 8963 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 13, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8963 :
    (8963 : ℕ).Prime ∧ logScale (8963 : ℚ) = 13 ∧
      (91008602679 : ℤ) = ⌊logCenter (8963 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8963 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8963 : Reach 8963 88430668387974 162261358011 := by
  have hr := row_8963
  have hl := log_bounds hr.1
    (by change logScale (8963 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8951) (T := 88339659785295) (U := 162243254545)
    (by norm_num) (by norm_num) hr.1 gap_8963
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8951

theorem gap_8969 : PrimeGap 8963 8969 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8969 :
    (8969 : ℕ).Prime ∧ logScale (8969 : ℚ) = 13 ∧
      (91015294627 : ℤ) = ⌊logCenter (8969 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8969 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8969 : Reach 8969 88521683682601 162279451383 := by
  have hr := row_8969
  have hl := log_bounds hr.1
    (by change logScale (8969 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8963) (T := 88430668387974) (U := 162261358011)
    (by norm_num) (by norm_num) hr.1 gap_8969
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8963

theorem gap_8971 : PrimeGap 8969 8971 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8971 :
    (8971 : ℕ).Prime ∧ logScale (8971 : ℚ) = 13 ∧
      (91017524281 : ℤ) = ⌊logCenter (8971 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8971 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8971 : Reach 8971 88612701206882 162297542738 := by
  have hr := row_8971
  have hl := log_bounds hr.1
    (by change logScale (8971 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8969) (T := 88521683682601) (U := 162279451383)
    (by norm_num) (by norm_num) hr.1 gap_8971
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8969

#print axioms reach_8971

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
