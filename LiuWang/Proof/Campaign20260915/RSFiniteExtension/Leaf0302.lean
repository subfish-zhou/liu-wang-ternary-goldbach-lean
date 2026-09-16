import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0301
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7417 : PrimeGap 7411 7417 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7417 :
    (7417 : ℕ).Prime ∧ logScale (7417 : ℚ) = 12 ∧
      (89115299386 : ℤ) = ⌊logCenter (7417 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7417 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7417 : Reach 7417 72845891922637 158857233840 := by
  have hr := row_7417
  have hl := log_bounds hr.1
    (by change logScale (7417 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7411) (T := 72756776623251) (U := 158835815849)
    (by norm_num) (by norm_num) hr.1 gap_7417
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7411

theorem gap_7433 : PrimeGap 7417 7433 :=
  (primeGap_of_factors (ds := [2, 3, 2, 41, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7433 :
    (7433 : ℕ).Prime ∧ logScale (7433 : ℚ) = 12 ∧
      (89136848216 : ℤ) = ⌊logCenter (7433 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7433 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7433 : Reach 7433 72935028770853 158878608603 := by
  have hr := row_7433
  have hl := log_bounds hr.1
    (by change logScale (7433 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7417) (T := 72845891922637) (U := 158857233840)
    (by norm_num) (by norm_num) hr.1 gap_7433
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7417

theorem gap_7451 : PrimeGap 7433 7451 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7451 :
    (7451 : ℕ).Prime ∧ logScale (7451 : ℚ) = 12 ∧
      (89161035274 : ℤ) = ⌊logCenter (7451 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7451 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7451 : Reach 7451 73024189806127 158899934591 := by
  have hr := row_7451
  have hl := log_bounds hr.1
    (by change logScale (7451 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7433) (T := 72935028770853) (U := 158878608603)
    (by norm_num) (by norm_num) hr.1 gap_7451
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7433

theorem gap_7457 : PrimeGap 7451 7457 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7457 :
    (7457 : ℕ).Prime ∧ logScale (7457 : ℚ) = 12 ∧
      (89169084644 : ℤ) = ⌊logCenter (7457 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7457 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7457 : Reach 7457 73113358890771 158921246278 := by
  have hr := row_7457
  have hl := log_bounds hr.1
    (by change logScale (7457 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7451) (T := 73024189806127) (U := 158899934591)
    (by norm_num) (by norm_num) hr.1 gap_7457
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7451

theorem gap_7459 : PrimeGap 7457 7459 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7459 :
    (7459 : ℕ).Prime ∧ logScale (7459 : ℚ) = 12 ∧
      (89171766328 : ℤ) = ⌊logCenter (7459 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7459 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7459 : Reach 7459 73202530657099 158942555107 := by
  have hr := row_7459
  have hl := log_bounds hr.1
    (by change logScale (7459 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7457) (T := 73113358890771) (U := 158921246278)
    (by norm_num) (by norm_num) hr.1 gap_7459
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7457

theorem gap_7477 : PrimeGap 7459 7477 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7477 :
    (7477 : ℕ).Prime ∧ logScale (7477 : ℚ) = 12 ∧
      (89195869178 : ℤ) = ⌊logCenter (7477 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7477 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7477 : Reach 7477 73291726526277 158963815481 := by
  have hr := row_7477
  have hl := log_bounds hr.1
    (by change logScale (7477 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7459) (T := 73202530657099) (U := 158942555107)
    (by norm_num) (by norm_num) hr.1 gap_7477
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7459

theorem gap_7481 : PrimeGap 7477 7481 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7481 :
    (7481 : ℕ).Prime ∧ logScale (7481 : ℚ) = 12 ∧
      (89201217487 : ℤ) = ⌊logCenter (7481 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7481 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7481 : Reach 7481 73380927743764 158985067328 := by
  have hr := row_7481
  have hl := log_bounds hr.1
    (by change logScale (7481 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7477) (T := 73291726526277) (U := 158963815481)
    (by norm_num) (by norm_num) hr.1 gap_7481
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7477

theorem gap_7487 : PrimeGap 7481 7487 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7487 :
    (7487 : ℕ).Prime ∧ logScale (7487 : ℚ) = 12 ∧
      (89209234591 : ℤ) = ⌊logCenter (7487 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7487 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7487 : Reach 7487 73470136978355 159006304981 := by
  have hr := row_7487
  have hl := log_bounds hr.1
    (by change logScale (7487 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7481) (T := 73380927743764) (U := 158985067328)
    (by norm_num) (by norm_num) hr.1 gap_7487
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7481

#print axioms reach_7487

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
