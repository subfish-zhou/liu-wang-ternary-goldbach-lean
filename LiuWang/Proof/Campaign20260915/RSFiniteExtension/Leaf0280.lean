import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block027
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_6823 : PrimeGap 6803 6823 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6823 :
    (6823 : ℕ).Prime ∧ logScale (6823 : ℚ) = 12 ∧
      (88280545336 : ℤ) = ⌊logCenter (6823 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6823 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6823 : Reach 6823 67170736761595 157430604683 := by
  have hr := row_6823
  have hl := log_bounds hr.1
    (by change logScale (6823 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6803) (T := 67082456216259) (U := 157407531166)
    (by norm_num) (by norm_num) hr.1 gap_6823
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6803

theorem gap_6827 : PrimeGap 6823 6827 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6827 :
    (6827 : ℕ).Prime ∧ logScale (6827 : ℚ) = 12 ∧
      (88286406142 : ℤ) = ⌊logCenter (6827 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6827 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6827 : Reach 6827 67259023167737 157453668060 := by
  have hr := row_6827
  have hl := log_bounds hr.1
    (by change logScale (6827 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6823) (T := 67170736761595) (U := 157430604683)
    (by norm_num) (by norm_num) hr.1 gap_6827
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6823

theorem gap_6829 : PrimeGap 6827 6829 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6829 :
    (6829 : ℕ).Prime ∧ logScale (6829 : ℚ) = 12 ∧
      (88289335258 : ℤ) = ⌊logCenter (6829 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6829 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6829 : Reach 6829 67347312502995 157476728059 := by
  have hr := row_6829
  have hl := log_bounds hr.1
    (by change logScale (6829 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6827) (T := 67259023167737) (U := 157453668060)
    (by norm_num) (by norm_num) hr.1 gap_6829
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6827

theorem gap_6833 : PrimeGap 6829 6833 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6833 :
    (6833 : ℕ).Prime ∧ logScale (6833 : ℚ) = 12 ∧
      (88295190916 : ℤ) = ⌊logCenter (6833 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6833 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6833 : Reach 6833 67435607693911 157499777932 := by
  have hr := row_6833
  have hl := log_bounds hr.1
    (by change logScale (6833 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6829) (T := 67347312502995) (U := 157476728059)
    (by norm_num) (by norm_num) hr.1 gap_6833
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6829

theorem gap_6841 : PrimeGap 6833 6841 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6841 :
    (6841 : ℕ).Prime ∧ logScale (6841 : ℚ) = 12 ∧
      (88306891956 : ℤ) = ⌊logCenter (6841 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6841 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6841 : Reach 6841 67523914585867 157522804216 := by
  have hr := row_6841
  have hl := log_bounds hr.1
    (by change logScale (6841 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6833) (T := 67435607693911) (U := 157499777932)
    (by norm_num) (by norm_num) hr.1 gap_6841
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6833

theorem gap_6857 : PrimeGap 6841 6857 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 41, 2, 3, 2, 13, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6857 :
    (6857 : ℕ).Prime ∧ logScale (6857 : ℚ) = 12 ∧
      (88330253041 : ℤ) = ⌊logCenter (6857 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6857 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6857 : Reach 6857 67612244838908 157545780121 := by
  have hr := row_6857
  have hl := log_bounds hr.1
    (by change logScale (6857 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6841) (T := 67523914585867) (U := 157522804216)
    (by norm_num) (by norm_num) hr.1 gap_6857
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6841

theorem gap_6863 : PrimeGap 6857 6863 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6863 :
    (6863 : ℕ).Prime ∧ logScale (6863 : ℚ) = 12 ∧
      (88338999397 : ℤ) = ⌊logCenter (6863 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6863 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6863 : Reach 6863 67700583838305 157568739285 := by
  have hr := row_6863
  have hl := log_bounds hr.1
    (by change logScale (6863 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6857) (T := 67612244838908) (U := 157545780121)
    (by norm_num) (by norm_num) hr.1 gap_6863
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6857

theorem gap_6869 : PrimeGap 6863 6869 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6869 :
    (6869 : ℕ).Prime ∧ logScale (6869 : ℚ) = 12 ∧
      (88347738110 : ℤ) = ⌊logCenter (6869 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6869 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6869 : Reach 6869 67788931576415 157591681734 := by
  have hr := row_6869
  have hl := log_bounds hr.1
    (by change logScale (6869 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6863) (T := 67700583838305) (U := 157568739285)
    (by norm_num) (by norm_num) hr.1 gap_6869
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6863

#print axioms reach_6869

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
