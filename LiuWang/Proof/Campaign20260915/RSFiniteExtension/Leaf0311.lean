import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0310
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7547 : PrimeGap 7541 7547 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7547 :
    (7547 : ℕ).Prime ∧ logScale (7547 : ℚ) = 12 ∧
      (89289054091 : ℤ) = ⌊logCenter (7547 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7547 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7547 : Reach 7547 74273427596970 159196707508 := by
  have hr := row_7547
  have hl := log_bounds hr.1
    (by change logScale (7547 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7541) (T := 74184138542879) (U := 159175613469)
    (by norm_num) (by norm_num) hr.1 gap_7547
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7541

theorem gap_7549 : PrimeGap 7547 7549 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7549 :
    (7549 : ℕ).Prime ∧ logScale (7549 : ℚ) = 12 ∧
      (89291703800 : ℤ) = ⌊logCenter (7549 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7549 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7549 : Reach 7549 74362719300770 159217798752 := by
  have hr := row_7549
  have hl := log_bounds hr.1
    (by change logScale (7549 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7547) (T := 74273427596970) (U := 159196707508)
    (by norm_num) (by norm_num) hr.1 gap_7549
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7547

theorem gap_7559 : PrimeGap 7549 7559 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7559 :
    (7559 : ℕ).Prime ∧ logScale (7559 : ℚ) = 12 ∧
      (89304941821 : ℤ) = ⌊logCenter (7559 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7559 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7559 : Reach 7559 74452024242591 159238864881 := by
  have hr := row_7559
  have hl := log_bounds hr.1
    (by change logScale (7559 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7549) (T := 74362719300770) (U := 159217798752)
    (by norm_num) (by norm_num) hr.1 gap_7559
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7549

theorem gap_7561 : PrimeGap 7559 7561 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7561 :
    (7561 : ℕ).Prime ∧ logScale (7561 : ℚ) = 12 ∧
      (89307587324 : ℤ) = ⌊logCenter (7561 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7561 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7561 : Reach 7561 74541331829915 159259928223 := by
  have hr := row_7561
  have hl := log_bounds hr.1
    (by change logScale (7561 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7559) (T := 74452024242591) (U := 159238864881)
    (by norm_num) (by norm_num) hr.1 gap_7561
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7559

theorem gap_7573 : PrimeGap 7561 7573 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 67, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7573 :
    (7573 : ℕ).Prime ∧ logScale (7573 : ℚ) = 12 ∧
      (89323445659 : ℤ) = ⌊logCenter (7573 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7573 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7573 : Reach 7573 74630655275574 159280960966 := by
  have hr := row_7573
  have hl := log_bounds hr.1
    (by change logScale (7573 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7561) (T := 74541331829915) (U := 159259928223)
    (by norm_num) (by norm_num) hr.1 gap_7573
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7561

theorem gap_7577 : PrimeGap 7573 7577 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7577 :
    (7577 : ℕ).Prime ∧ logScale (7577 : ℚ) = 12 ∧
      (89328726188 : ℤ) = ⌊logCenter (7577 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7577 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7577 : Reach 7577 74719984001762 159301985381 := by
  have hr := row_7577
  have hl := log_bounds hr.1
    (by change logScale (7577 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7573) (T := 74630655275574) (U := 159280960966)
    (by norm_num) (by norm_num) hr.1 gap_7577
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7573

theorem gap_7583 : PrimeGap 7577 7583 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7583 :
    (7583 : ℕ).Prime ∧ logScale (7583 : ℚ) = 12 ∧
      (89336641755 : ℤ) = ⌊logCenter (7583 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7583 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7583 : Reach 7583 74809320643517 159322995931 := by
  have hr := row_7583
  have hl := log_bounds hr.1
    (by change logScale (7583 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7577) (T := 74719984001762) (U := 159301985381)
    (by norm_num) (by norm_num) hr.1 gap_7583
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7577

theorem gap_7589 : PrimeGap 7583 7589 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7589 :
    (7589 : ℕ).Prime ∧ logScale (7589 : ℚ) = 12 ∧
      (89344551062 : ℤ) = ⌊logCenter (7589 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7589 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7589 : Reach 7589 74898665194579 159343992636 := by
  have hr := row_7589
  have hl := log_bounds hr.1
    (by change logScale (7589 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7583) (T := 74809320643517) (U := 159322995931)
    (by norm_num) (by norm_num) hr.1 gap_7589
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7583

#print axioms reach_7589

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
