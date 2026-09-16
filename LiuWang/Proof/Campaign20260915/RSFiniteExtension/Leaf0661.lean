import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0660
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15377 : PrimeGap 15373 15377 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15377 :
    (15377 : ℕ).Prime ∧ logScale (15377 : ℚ) = 13 ∧
      (96406281621 : ℤ) = ⌊logCenter (15377 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15377 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15377 : Reach 15377 152588560434908 171877424014 := by
  have hr := row_15377
  have hl := log_bounds hr.1
    (by change logScale (15377 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15373) (T := 152492154153287) (U := 171866246448)
    (by norm_num) (by norm_num) hr.1 gap_15377
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15373

theorem gap_15383 : PrimeGap 15377 15383 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15383 :
    (15383 : ℕ).Prime ∧ logScale (15383 : ℚ) = 13 ∧
      (96410182791 : ℤ) = ⌊logCenter (15383 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15383 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15383 : Reach 15383 152684970617699 171888597947 := by
  have hr := row_15383
  have hl := log_bounds hr.1
    (by change logScale (15383 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15377) (T := 152588560434908) (U := 171877424014)
    (by norm_num) (by norm_num) hr.1 gap_15383
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15377

theorem gap_15391 : PrimeGap 15383 15391 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15391 :
    (15391 : ℕ).Prime ∧ logScale (15391 : ℚ) = 13 ∧
      (96415381985 : ℤ) = ⌊logCenter (15391 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15391 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15391 : Reach 15391 152781385999684 171899766797 := by
  have hr := row_15391
  have hl := log_bounds hr.1
    (by change logScale (15391 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15383) (T := 152684970617699) (U := 171888597947)
    (by norm_num) (by norm_num) hr.1 gap_15391
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15383

theorem gap_15401 : PrimeGap 15391 15401 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 89, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15401 :
    (15401 : ℕ).Prime ∧ logScale (15401 : ℚ) = 13 ∧
      (96421877179 : ℤ) = ⌊logCenter (15401 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15401 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15401 : Reach 15401 152877807876863 171910929120 := by
  have hr := row_15401
  have hl := log_bounds hr.1
    (by change logScale (15401 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15391) (T := 152781385999684) (U := 171899766797)
    (by norm_num) (by norm_num) hr.1 gap_15401
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15391

theorem gap_15413 : PrimeGap 15401 15413 :=
  (primeGap_of_factors (ds := [2, 73, 2, 3, 2, 7, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15413 :
    (15413 : ℕ).Prime ∧ logScale (15413 : ℚ) = 13 ∧
      (96429665847 : ℤ) = ⌊logCenter (15413 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15413 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15413 : Reach 15413 152974237542710 171922083476 := by
  have hr := row_15413
  have hl := log_bounds hr.1
    (by change logScale (15413 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15401) (T := 152877807876863) (U := 171910929120)
    (by norm_num) (by norm_num) hr.1 gap_15413
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15401

theorem gap_15427 : PrimeGap 15413 15427 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15427 :
    (15427 : ℕ).Prime ∧ logScale (15427 : ℚ) = 13 ∧
      (96438744966 : ℤ) = ⌊logCenter (15427 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15427 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15427 : Reach 15427 153070676287676 171933228432 := by
  have hr := row_15427
  have hl := log_bounds hr.1
    (by change logScale (15427 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15413) (T := 152974237542710) (U := 171922083476)
    (by norm_num) (by norm_num) hr.1 gap_15427
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15413

theorem gap_15439 : PrimeGap 15427 15439 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 11, 2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15439 :
    (15439 : ℕ).Prime ∧ logScale (15439 : ℚ) = 13 ∧
      (96446520512 : ℤ) = ⌊logCenter (15439 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15439 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15439 : Reach 15439 153167122808188 171944365447 := by
  have hr := row_15439
  have hl := log_bounds hr.1
    (by change logScale (15439 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15427) (T := 153070676287676) (U := 171933228432)
    (by norm_num) (by norm_num) hr.1 gap_15439
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15427

theorem gap_15443 : PrimeGap 15439 15443 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15443 :
    (15443 : ℕ).Prime ∧ logScale (15443 : ℚ) = 13 ∧
      (96449111018 : ℤ) = ⌊logCenter (15443 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15443 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15443 : Reach 15443 153263571919206 171955500298 := by
  have hr := row_15443
  have hl := log_bounds hr.1
    (by change logScale (15443 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15439) (T := 153167122808188) (U := 171944365447)
    (by norm_num) (by norm_num) hr.1 gap_15443
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15439

#print axioms reach_15443

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
