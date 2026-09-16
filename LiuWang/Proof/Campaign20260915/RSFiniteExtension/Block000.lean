import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Start

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block000 : List ℕ := [1427, 1429, 1433, 1439]

theorem complete_Block000 :
    ∀ p ∈ Finset.Ioc 1423 1439, p.Prime ↔ p ∈ primes_Block000 := by
  decide +kernel

theorem row_1427 :
    (1427 : ℕ).Prime ∧ logScale (1427 : ℚ) = 10 ∧
      (72633296148 : ℤ) = ⌊logCenter (1427 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1427 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1427 : Reach 1427 13600860786523 129584337654 := by
  have hr := row_1427
  have hl := log_bounds hr.1
    (by change logScale (1427 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1423) (T := 13528227490375) (U := 129493528727)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1423

theorem row_1429 :
    (1429 : ℕ).Prime ∧ logScale (1429 : ℚ) = 10 ∧
      (72647301753 : ℤ) = ⌊logCenter (1429 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1429 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1429 : Reach 1429 13673508088276 129675082989 := by
  have hr := row_1429
  have hl := log_bounds hr.1
    (by change logScale (1429 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1427) (T := 13600860786523) (U := 129584337654)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1427

theorem row_1433 :
    (1433 : ℕ).Prime ∧ logScale (1433 : ℚ) = 10 ∧
      (72675254252 : ℤ) = ⌊logCenter (1433 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1433 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1433 : Reach 1433 13746183342528 129765638215 := by
  have hr := row_1433
  have hl := log_bounds hr.1
    (by change logScale (1433 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1429) (T := 13673508088276) (U := 129675082989)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1429

theorem row_1439 :
    (1439 : ℕ).Prime ∧ logScale (1439 : ℚ) = 10 ∧
      (72717037042 : ℤ) = ⌊logCenter (1439 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1439 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1439 : Reach 1439 13818900379570 129855878576 := by
  have hr := row_1439
  have hl := log_bounds hr.1
    (by change logScale (1439 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1433) (T := 13746183342528) (U := 129765638215)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1433

#print axioms reach_1439

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
