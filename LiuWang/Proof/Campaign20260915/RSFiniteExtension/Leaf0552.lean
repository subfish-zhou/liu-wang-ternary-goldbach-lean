import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0551
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12941 : PrimeGap 12923 12941 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 67, 2, 3, 2, 5, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12941 :
    (12941 : ℕ).Prime ∧ logScale (12941 : ℚ) = 13 ∧
      (94681558414 : ℤ) = ⌊logCenter (12941 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12941 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12941 : Reach 12941 128119061916929 168794577741 := by
  have hr := row_12941
  have hl := log_bounds hr.1
    (by change logScale (12941 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12923) (T := 128024380358515) (U := 168781534345)
    (by norm_num) (by norm_num) hr.1 gap_12941
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12923

theorem gap_12953 : PrimeGap 12941 12953 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 11, 2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12953 :
    (12953 : ℕ).Prime ∧ logScale (12953 : ℚ) = 13 ∧
      (94690826971 : ℤ) = ⌊logCenter (12953 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12953 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12953 : Reach 12953 128213752743900 168807610059 := by
  have hr := row_12953
  have hl := log_bounds hr.1
    (by change logScale (12953 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12941) (T := 128119061916929) (U := 168794577741)
    (by norm_num) (by norm_num) hr.1 gap_12953
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12941

theorem gap_12959 : PrimeGap 12953 12959 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12959 :
    (12959 : ℕ).Prime ∧ logScale (12959 : ℚ) = 13 ∧
      (94695458030 : ℤ) = ⌊logCenter (12959 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12959 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12959 : Reach 12959 128308448201930 168820637348 := by
  have hr := row_12959
  have hl := log_bounds hr.1
    (by change logScale (12959 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12953) (T := 128213752743900) (U := 168807610059)
    (by norm_num) (by norm_num) hr.1 gap_12959
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12953

theorem gap_12967 : PrimeGap 12959 12967 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12967 :
    (12967 : ℕ).Prime ∧ logScale (12967 : ℚ) = 13 ∧
      (94701629441 : ℤ) = ⌊logCenter (12967 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12967 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12967 : Reach 12967 128403149831371 168833657604 := by
  have hr := row_12967
  have hl := log_bounds hr.1
    (by change logScale (12967 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12959) (T := 128308448201930) (U := 168820637348)
    (by norm_num) (by norm_num) hr.1 gap_12967
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12959

theorem gap_12973 : PrimeGap 12967 12973 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12973 :
    (12973 : ℕ).Prime ∧ logScale (12973 : ℚ) = 13 ∧
      (94706255501 : ℤ) = ⌊logCenter (12973 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12973 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12973 : Reach 12973 128497856086872 168846672842 := by
  have hr := row_12973
  have hl := log_bounds hr.1
    (by change logScale (12973 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12967) (T := 128403149831371) (U := 168833657604)
    (by norm_num) (by norm_num) hr.1 gap_12973
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12967

theorem gap_12979 : PrimeGap 12973 12979 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12979 :
    (12979 : ℕ).Prime ∧ logScale (12979 : ℚ) = 13 ∧
      (94710879423 : ℤ) = ⌊logCenter (12979 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12979 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12979 : Reach 12979 128592566966295 168859683065 := by
  have hr := row_12979
  have hl := log_bounds hr.1
    (by change logScale (12979 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12973) (T := 128497856086872) (U := 168846672842)
    (by norm_num) (by norm_num) hr.1 gap_12979
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12973

theorem gap_12983 : PrimeGap 12979 12983 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12983 :
    (12983 : ℕ).Prime ∧ logScale (12983 : ℚ) = 13 ∧
      (94713960849 : ℤ) = ⌊logCenter (12983 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12983 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12983 : Reach 12983 128687280927144 168872690282 := by
  have hr := row_12983
  have hl := log_bounds hr.1
    (by change logScale (12983 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12979) (T := 128592566966295) (U := 168859683065)
    (by norm_num) (by norm_num) hr.1 gap_12983
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12979

theorem gap_13001 : PrimeGap 12983 13001 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 31, 2, 11, 2, 3, 2, 5, 2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13001 :
    (13001 : ℕ).Prime ∧ logScale (13001 : ℚ) = 13 ∧
      (94727815531 : ℤ) = ⌊logCenter (13001 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13001 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13001 : Reach 13001 128782008742675 168885680489 := by
  have hr := row_13001
  have hl := log_bounds hr.1
    (by change logScale (13001 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12983) (T := 128687280927144) (U := 168872690282)
    (by norm_num) (by norm_num) hr.1 gap_13001
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12983

#print axioms reach_13001

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
