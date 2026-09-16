import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block026
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_6599 : PrimeGap 6581 6599 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 7, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6599 :
    (6599 : ℕ).Prime ∧ logScale (6599 : ℚ) = 12 ∧
      (87946733982 : ℤ) = ⌊logCenter (6599 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6599 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6599 : Reach 6599 65055836610040 156868865528 := by
  have hr := row_6599
  have hl := log_bounds hr.1
    (by change logScale (6599 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6581) (T := 64967889876058) (U := 156845093916)
    (by norm_num) (by norm_num) hr.1 gap_6599
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6581

theorem gap_6607 : PrimeGap 6599 6607 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6607 :
    (6607 : ℕ).Prime ∧ logScale (6607 : ℚ) = 12 ∧
      (87958849689 : ℤ) = ⌊logCenter (6607 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6607 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6607 : Reach 6607 65143795459729 156892611951 := by
  have hr := row_6607
  have hl := log_bounds hr.1
    (by change logScale (6607 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6599) (T := 65055836610040) (U := 156868865528)
    (by norm_num) (by norm_num) hr.1 gap_6607
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6599

theorem gap_6619 : PrimeGap 6607 6619 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 17, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6619 :
    (6619 : ℕ).Prime ∧ logScale (6619 : ℚ) = 12 ∧
      (87976995769 : ℤ) = ⌊logCenter (6619 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6619 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6619 : Reach 6619 65231772455498 156916318904 := by
  have hr := row_6619
  have hl := log_bounds hr.1
    (by change logScale (6619 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6607) (T := 65143795459729) (U := 156892611951)
    (by norm_num) (by norm_num) hr.1 gap_6619
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6607

theorem gap_6637 : PrimeGap 6619 6637 :=
  (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6637 :
    (6637 : ℕ).Prime ∧ logScale (6637 : ℚ) = 12 ∧
      (88004153300 : ℤ) = ⌊logCenter (6637 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6637 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6637 : Reach 6637 65319776608798 156939965125 := by
  have hr := row_6637
  have hl := log_bounds hr.1
    (by change logScale (6637 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6619) (T := 65231772455498) (U := 156916318904)
    (by norm_num) (by norm_num) hr.1 gap_6637
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6619

theorem gap_6653 : PrimeGap 6637 6653 :=
  (primeGap_of_factors (ds := [2, 3, 2, 29, 2, 7, 2, 3, 2, 17, 2, 61, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6653 :
    (6653 : ℕ).Prime ∧ logScale (6653 : ℚ) = 12 ∧
      (88028231566 : ℤ) = ⌊logCenter (6653 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6653 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6653 : Reach 6653 65407804840364 156963558025 := by
  have hr := row_6653
  have hl := log_bounds hr.1
    (by change logScale (6653 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6637) (T := 65319776608798) (U := 156939965125)
    (by norm_num) (by norm_num) hr.1 gap_6653
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6637

theorem gap_6659 : PrimeGap 6653 6659 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6659 :
    (6659 : ℕ).Prime ∧ logScale (6659 : ℚ) = 12 ∧
      (88037245989 : ℤ) = ⌊logCenter (6659 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6659 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6659 : Reach 6659 65495842086353 156987133207 := by
  have hr := row_6659
  have hl := log_bounds hr.1
    (by change logScale (6659 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6653) (T := 65407804840364) (U := 156963558025)
    (by norm_num) (by norm_num) hr.1 gap_6659
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6653

theorem gap_6661 : PrimeGap 6659 6661 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6661 :
    (6661 : ℕ).Prime ∧ logScale (6661 : ℚ) = 12 ∧
      (88040248992 : ℤ) = ⌊logCenter (6661 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6661 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6661 : Reach 6661 65583882335345 157010704849 := by
  have hr := row_6661
  have hl := log_bounds hr.1
    (by change logScale (6661 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6659) (T := 65495842086353) (U := 156987133207)
    (by norm_num) (by norm_num) hr.1 gap_6661
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6659

theorem gap_6673 : PrimeGap 6661 6673 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6673 :
    (6673 : ℕ).Prime ∧ logScale (6673 : ℚ) = 12 ∧
      (88058248097 : ℤ) = ⌊logCenter (6673 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6673 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6673 : Reach 6673 65671940583442 157034237629 := by
  have hr := row_6673
  have hl := log_bounds hr.1
    (by change logScale (6673 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6661) (T := 65583882335345) (U := 157010704849)
    (by norm_num) (by norm_num) hr.1 gap_6673
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6661

#print axioms reach_6673

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
