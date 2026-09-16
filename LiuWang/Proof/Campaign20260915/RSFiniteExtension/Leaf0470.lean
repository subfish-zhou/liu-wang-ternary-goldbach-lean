import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block046
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10979 : PrimeGap 10973 10979 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10979 :
    (10979 : ℕ).Prime ∧ logScale (10979 : ℚ) = 13 ∧
      (93037396328 : ℤ) = ⌊logCenter (10979 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10979 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10979 : Reach 10979 108587321444746 165883772000 := by
  have hr := row_10979
  have hl := log_bounds hr.1
    (by change logScale (10979 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10973) (T := 108494284048418) (U := 165868662812)
    (by norm_num) (by norm_num) hr.1 gap_10979
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10973

theorem gap_10987 : PrimeGap 10979 10987 :=
  (primeGap_of_factors (ds := [2, 79, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10987 :
    (10987 : ℕ).Prime ∧ logScale (10987 : ℚ) = 13 ∧
      (93044680313 : ℤ) = ⌊logCenter (10987 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10987 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10987 : Reach 10987 108680366125059 165898871561 := by
  have hr := row_10987
  have hl := log_bounds hr.1
    (by change logScale (10987 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10979) (T := 108587321444746) (U := 165883772000)
    (by norm_num) (by norm_num) hr.1 gap_10987
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10979

theorem gap_10993 : PrimeGap 10987 10993 :=
  (primeGap_of_factors (ds := [2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10993 :
    (10993 : ℕ).Prime ∧ logScale (10993 : ℚ) = 13 ∧
      (93050139821 : ℤ) = ⌊logCenter (10993 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10993 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10993 : Reach 10993 108773416264880 165913964254 := by
  have hr := row_10993
  have hl := log_bounds hr.1
    (by change logScale (10993 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10987) (T := 108680366125059) (U := 165898871561)
    (by norm_num) (by norm_num) hr.1 gap_10993
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10987

theorem gap_11003 : PrimeGap 10993 11003 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11003 :
    (11003 : ℕ).Prime ∧ logScale (11003 : ℚ) = 13 ∧
      (93059232384 : ℤ) = ⌊logCenter (11003 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11003 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11003 : Reach 11003 108866475497264 165929044600 := by
  have hr := row_11003
  have hl := log_bounds hr.1
    (by change logScale (11003 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10993) (T := 108773416264880) (U := 165913964254)
    (by norm_num) (by norm_num) hr.1 gap_11003
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10993

theorem gap_11027 : PrimeGap 11003 11027 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 101, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 103, 2, 73, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11027 :
    (11027 : ℕ).Prime ∧ logScale (11027 : ℚ) = 13 ∧
      (93081020863 : ℤ) = ⌊logCenter (11027 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11027 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11027 : Reach 11027 108959556518127 165944093489 := by
  have hr := row_11027
  have hl := log_bounds hr.1
    (by change logScale (11027 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11003) (T := 108866475497264) (U := 165929044600)
    (by norm_num) (by norm_num) hr.1 gap_11027
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11003

theorem gap_11047 : PrimeGap 11027 11047 :=
  (primeGap_of_factors (ds := [2, 41, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 61, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11047 :
    (11047 : ℕ).Prime ∧ logScale (11047 : ℚ) = 13 ∧
      (93099141734 : ℤ) = ⌊logCenter (11047 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11047 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11047 : Reach 11047 109052655659861 165959116493 := by
  have hr := row_11047
  have hl := log_bounds hr.1
    (by change logScale (11047 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11027) (T := 108959556518127) (U := 165944093489)
    (by norm_num) (by norm_num) hr.1 gap_11047
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11027

theorem gap_11057 : PrimeGap 11047 11057 :=
  (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11057 :
    (11057 : ℕ).Prime ∧ logScale (11057 : ℚ) = 13 ∧
      (93108189871 : ℤ) = ⌊logCenter (11057 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11057 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11057 : Reach 11057 109145763849732 165974127267 := by
  have hr := row_11057
  have hl := log_bounds hr.1
    (by change logScale (11057 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11047) (T := 109052655659861) (U := 165959116493)
    (by norm_num) (by norm_num) hr.1 gap_11057
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11047

theorem gap_11059 : PrimeGap 11057 11059 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11059 :
    (11059 : ℕ).Prime ∧ logScale (11059 : ℚ) = 13 ∧
      (93109998516 : ℤ) = ⌊logCenter (11059 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11059 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11059 : Reach 11059 109238873848248 165989136684 := by
  have hr := row_11059
  have hl := log_bounds hr.1
    (by change logScale (11059 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11057) (T := 109145763849732) (U := 165974127267)
    (by norm_num) (by norm_num) hr.1 gap_11059
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11057

#print axioms reach_11059

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
