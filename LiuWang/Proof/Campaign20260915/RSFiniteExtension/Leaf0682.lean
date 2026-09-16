import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0681
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15901 : PrimeGap 15889 15901 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15901 :
    (15901 : ℕ).Prime ∧ logScale (15901 : ℚ) = 13 ∧
      (96741372759 : ℤ) = ⌊logCenter (15901 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15901 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15901 : Reach 15901 157997011247112 172493770027 := by
  have hr := row_15901
  have hl := log_bounds hr.1
    (by change logScale (15901 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15889) (T := 157900269874353) (U := 172482922044)
    (by norm_num) (by norm_num) hr.1 gap_15901
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15889

theorem gap_15907 : PrimeGap 15901 15907 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15907 :
    (15907 : ℕ).Prime ∧ logScale (15907 : ℚ) = 13 ∧
      (96745145395 : ℤ) = ⌊logCenter (15907 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15907 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15907 : Reach 15907 158093756392507 172504614600 := by
  have hr := row_15907
  have hl := log_bounds hr.1
    (by change logScale (15907 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15901) (T := 157997011247112) (U := 172493770027)
    (by norm_num) (by norm_num) hr.1 gap_15907
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15901

theorem gap_15913 : PrimeGap 15907 15913 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15913 :
    (15913 : ℕ).Prime ∧ logScale (15913 : ℚ) = 13 ∧
      (96748916608 : ℤ) = ⌊logCenter (15913 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15913 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15913 : Reach 15913 158190505309115 172515455765 := by
  have hr := row_15913
  have hl := log_bounds hr.1
    (by change logScale (15913 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15907) (T := 158093756392507) (U := 172504614600)
    (by norm_num) (by norm_num) hr.1 gap_15913
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15907

theorem gap_15919 : PrimeGap 15913 15919 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15919 :
    (15919 : ℕ).Prime ∧ logScale (15919 : ℚ) = 13 ∧
      (96752686399 : ℤ) = ⌊logCenter (15919 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15919 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15919 : Reach 15919 158287257995514 172526293525 := by
  have hr := row_15919
  have hl := log_bounds hr.1
    (by change logScale (15919 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15913) (T := 158190505309115) (U := 172515455765)
    (by norm_num) (by norm_num) hr.1 gap_15919
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15913

theorem gap_15923 : PrimeGap 15919 15923 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15923 :
    (15923 : ℕ).Prime ∧ logScale (15923 : ℚ) = 13 ∧
      (96755198804 : ℤ) = ⌊logCenter (15923 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15923 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15923 : Reach 15923 158384013194318 172537129243 := by
  have hr := row_15923
  have hl := log_bounds hr.1
    (by change logScale (15923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15919) (T := 158287257995514) (U := 172526293525)
    (by norm_num) (by norm_num) hr.1 gap_15923
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15919

theorem gap_15937 : PrimeGap 15923 15937 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2, 89, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15937 :
    (15937 : ℕ).Prime ∧ logScale (15937 : ℚ) = 13 ∧
      (96763987254 : ℤ) = ⌊logCenter (15937 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15937 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15937 : Reach 15937 158480777181572 172547956122 := by
  have hr := row_15937
  have hl := log_bounds hr.1
    (by change logScale (15937 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15923) (T := 158384013194318) (U := 172537129243)
    (by norm_num) (by norm_num) hr.1 gap_15937
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15923

theorem gap_15959 : PrimeGap 15937 15959 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 107, 2, 3, 2, 37, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15959 :
    (15959 : ℕ).Prime ∧ logScale (15959 : ℚ) = 13 ∧
      (96777782090 : ℤ) = ⌊logCenter (15959 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15959 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15959 : Reach 15959 158577554963662 172558768753 := by
  have hr := row_15959
  have hl := log_bounds hr.1
    (by change logScale (15959 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15937) (T := 158480777181572) (U := 172547956122)
    (by norm_num) (by norm_num) hr.1 gap_15959
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15937

theorem gap_15971 : PrimeGap 15959 15971 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15971 :
    (15971 : ℕ).Prime ∧ logScale (15971 : ℚ) = 13 ∧
      (96785298532 : ℤ) = ⌊logCenter (15971 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15971 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15971 : Reach 15971 158674340262194 172569573936 := by
  have hr := row_15971
  have hl := log_bounds hr.1
    (by change logScale (15971 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15959) (T := 158577554963662) (U := 172558768753)
    (by norm_num) (by norm_num) hr.1 gap_15971
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15959

#print axioms reach_15971

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
