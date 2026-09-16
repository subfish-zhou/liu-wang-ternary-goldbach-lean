import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0331
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8059 : PrimeGap 8053 8059 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8059 :
    (8059 : ℕ).Prime ∧ logScale (8059 : ℚ) = 12 ∧
      (89945447551 : ℤ) = ⌊logCenter (8059 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8059 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8059 : Reach 8059 79290969982534 160346342590 := by
  have hr := row_8059
  have hl := log_bounds hr.1
    (by change logScale (8059 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8053) (T := 79201024534983) (U := 160326446034)
    (by norm_num) (by norm_num) hr.1 gap_8059
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8053

theorem gap_8069 : PrimeGap 8059 8069 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8069 :
    (8069 : ℕ).Prime ∧ logScale (8069 : ℚ) = 12 ∧
      (89957848347 : ℤ) = ⌊logCenter (8069 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8069 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8069 : Reach 8069 79380927830881 160366216951 := by
  have hr := row_8069
  have hl := log_bounds hr.1
    (by change logScale (8069 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8059) (T := 79290969982534) (U := 160346342590)
    (by norm_num) (by norm_num) hr.1 gap_8069
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8059

theorem gap_8081 : PrimeGap 8069 8081 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8081 :
    (8081 : ℕ).Prime ∧ logScale (8081 : ℚ) = 12 ∧
      (89972709031 : ℤ) = ⌊logCenter (8081 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8081 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8081 : Reach 8081 79470900539912 160386064256 := by
  have hr := row_8081
  have hl := log_bounds hr.1
    (by change logScale (8081 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8069) (T := 79380927830881) (U := 160366216951)
    (by norm_num) (by norm_num) hr.1 gap_8081
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8069

theorem gap_8087 : PrimeGap 8081 8087 :=
  (primeGap_of_factors (ds := [2, 59, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8087 :
    (8087 : ℕ).Prime ∧ logScale (8087 : ℚ) = 12 ∧
      (89980131099 : ℤ) = ⌊logCenter (8087 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8087 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8087 : Reach 8087 79560880671011 160405899288 := by
  have hr := row_8087
  have hl := log_bounds hr.1
    (by change logScale (8087 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8081) (T := 79470900539912) (U := 160386064256)
    (by norm_num) (by norm_num) hr.1 gap_8087
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8081

theorem gap_8089 : PrimeGap 8087 8089 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8089 :
    (8089 : ℕ).Prime ∧ logScale (8089 : ℚ) = 12 ∧
      (89982603898 : ℤ) = ⌊logCenter (8089 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8089 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8089 : Reach 8089 79650863274909 160425731868 := by
  have hr := row_8089
  have hl := log_bounds hr.1
    (by change logScale (8089 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8087) (T := 79560880671011) (U := 160405899288)
    (by norm_num) (by norm_num) hr.1 gap_8089
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8087

theorem gap_8093 : PrimeGap 8089 8093 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8093 :
    (8093 : ℕ).Prime ∧ logScale (8093 : ℚ) = 12 ∧
      (89987547663 : ℤ) = ⌊logCenter (8093 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8093 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8093 : Reach 8093 79740850822572 160445557095 := by
  have hr := row_8093
  have hl := log_bounds hr.1
    (by change logScale (8093 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8089) (T := 79650863274909) (U := 160425731868)
    (by norm_num) (by norm_num) hr.1 gap_8093
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8089

theorem gap_8101 : PrimeGap 8093 8101 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8101 :
    (8101 : ℕ).Prime ∧ logScale (8101 : ℚ) = 12 ∧
      (89997427867 : ℤ) = ⌊logCenter (8101 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8101 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8101 : Reach 8101 79830848250439 160465365189 := by
  have hr := row_8101
  have hl := log_bounds hr.1
    (by change logScale (8101 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8093) (T := 79740850822572) (U := 160445557095)
    (by norm_num) (by norm_num) hr.1 gap_8101
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8093

theorem gap_8111 : PrimeGap 8101 8111 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8111 :
    (8111 : ℕ).Prime ∧ logScale (8111 : ℚ) = 12 ∧
      (90009764409 : ℤ) = ⌊logCenter (8111 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8111 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8111 : Reach 8111 79920858014848 160485151301 := by
  have hr := row_8111
  have hl := log_bounds hr.1
    (by change logScale (8111 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8101) (T := 79830848250439) (U := 160465365189)
    (by norm_num) (by norm_num) hr.1 gap_8111
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8101

#print axioms reach_8111

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
