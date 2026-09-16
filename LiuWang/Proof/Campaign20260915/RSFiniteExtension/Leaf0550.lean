import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block054
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12791 : PrimeGap 12781 12791 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12791 :
    (12791 : ℕ).Prime ∧ logScale (12791 : ℚ) = 13 ∧
      (94564970742 : ℤ) = ⌊logCenter (12791 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12791 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12791 : Reach 12791 126604996280327 168584906667 := by
  have hr := row_12791
  have hl := log_bounds hr.1
    (by change logScale (12791 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12781) (T := 126510431309585) (U := 168571726704)
    (by norm_num) (by norm_num) hr.1 gap_12791
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12781

theorem gap_12799 : PrimeGap 12791 12799 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 67, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12799 :
    (12799 : ℕ).Prime ∧ logScale (12799 : ℚ) = 13 ∧
      (94571223184 : ℤ) = ⌊logCenter (12799 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12799 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12799 : Reach 12799 126699567503511 168598079422 := by
  have hr := row_12799
  have hl := log_bounds hr.1
    (by change logScale (12799 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12791) (T := 126604996280327) (U := 168584906667)
    (by norm_num) (by norm_num) hr.1 gap_12799
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12791

theorem gap_12809 : PrimeGap 12799 12809 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12809 :
    (12809 : ℕ).Prime ∧ logScale (12809 : ℚ) = 13 ∧
      (94579033244 : ℤ) = ⌊logCenter (12809 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12809 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12809 : Reach 12809 126794146536755 168611242920 := by
  have hr := row_12809
  have hl := log_bounds hr.1
    (by change logScale (12809 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12799) (T := 126699567503511) (U := 168598079422)
    (by norm_num) (by norm_num) hr.1 gap_12809
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12799

theorem gap_12821 : PrimeGap 12809 12821 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12821 :
    (12821 : ℕ).Prime ∧ logScale (12821 : ℚ) = 13 ∧
      (94588397271 : ℤ) = ⌊logCenter (12821 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12821 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12821 : Reach 12821 126888734934026 168624395124 := by
  have hr := row_12821
  have hl := log_bounds hr.1
    (by change logScale (12821 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12809) (T := 126794146536755) (U := 168611242920)
    (by norm_num) (by norm_num) hr.1 gap_12821
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12809

theorem gap_12823 : PrimeGap 12821 12823 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12823 :
    (12823 : ℕ).Prime ∧ logScale (12823 : ℚ) = 13 ∧
      (94589957090 : ℤ) = ⌊logCenter (12823 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12823 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12823 : Reach 12823 126983324891116 168637546302 := by
  have hr := row_12823
  have hl := log_bounds hr.1
    (by change logScale (12823 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12821) (T := 126888734934026) (U := 168624395124)
    (by norm_num) (by norm_num) hr.1 gap_12823
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12821

theorem gap_12829 : PrimeGap 12823 12829 :=
  (primeGap_of_factors (ds := [2, 3, 2, 101, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12829 :
    (12829 : ℕ).Prime ∧ logScale (12829 : ℚ) = 13 ∧
      (94594635088 : ℤ) = ⌊logCenter (12829 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12829 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12829 : Reach 12829 127077919526204 168650692354 := by
  have hr := row_12829
  have hl := log_bounds hr.1
    (by change logScale (12829 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12823) (T := 126983324891116) (U := 168637546302)
    (by norm_num) (by norm_num) hr.1 gap_12829
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12823

theorem gap_12841 : PrimeGap 12829 12841 :=
  (primeGap_of_factors (ds := [2, 3, 2, 41, 2, 5, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12841 :
    (12841 : ℕ).Prime ∧ logScale (12841 : ℚ) = 13 ∧
      (94603984524 : ℤ) = ⌊logCenter (12841 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12841 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12841 : Reach 12841 127172523510728 168663827144 := by
  have hr := row_12841
  have hl := log_bounds hr.1
    (by change logScale (12841 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12829) (T := 127077919526204) (U := 168650692354)
    (by norm_num) (by norm_num) hr.1 gap_12841
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12829

theorem gap_12853 : PrimeGap 12841 12853 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 29, 2, 3, 2, 71, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12853 :
    (12853 : ℕ).Prime ∧ logScale (12853 : ℚ) = 13 ∧
      (94613325227 : ℤ) = ⌊logCenter (12853 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12853 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12853 : Reach 12853 127267136835955 168676950692 := by
  have hr := row_12853
  have hl := log_bounds hr.1
    (by change logScale (12853 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12841) (T := 127172523510728) (U := 168663827144)
    (by norm_num) (by norm_num) hr.1 gap_12853
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12841

#print axioms reach_12853

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
