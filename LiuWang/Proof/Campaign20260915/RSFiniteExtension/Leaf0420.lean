import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block041
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9833 : PrimeGap 9829 9833 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9833 :
    (9833 : ℕ).Prime ∧ logScale (9833 : ℚ) = 13 ∧
      (91934993514 : ℤ) = ⌊logCenter (9833 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9833 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9833 : Reach 9833 97487800051121 163979760940 := by
  have hr := row_9833
  have hl := log_bounds hr.1
    (by change logScale (9833 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9829) (T := 97395865057607) (U := 163963084466)
    (by norm_num) (by norm_num) hr.1 gap_9833
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9829

theorem gap_9839 : PrimeGap 9833 9839 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9839 :
    (9839 : ℕ).Prime ∧ logScale (9839 : ℚ) = 13 ∧
      (91941093554 : ℤ) = ⌊logCenter (9839 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9839 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9839 : Reach 9839 97579741144675 163996428938 := by
  have hr := row_9839
  have hl := log_bounds hr.1
    (by change logScale (9839 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9833) (T := 97487800051121) (U := 163979760940)
    (by norm_num) (by norm_num) hr.1 gap_9839
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9833

theorem gap_9851 : PrimeGap 9839 9851 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2, 43, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9851 :
    (9851 : ℕ).Prime ∧ logScale (9851 : ℚ) = 13 ∧
      (91953282484 : ℤ) = ⌊logCenter (9851 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9851 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9851 : Reach 9851 97671694427159 164013078322 := by
  have hr := row_9851
  have hl := log_bounds hr.1
    (by change logScale (9851 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9839) (T := 97579741144675) (U := 163996428938)
    (by norm_num) (by norm_num) hr.1 gap_9851
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9839

theorem gap_9857 : PrimeGap 9851 9857 :=
  (primeGap_of_factors (ds := [2, 59, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9857 :
    (9857 : ℕ).Prime ∧ logScale (9857 : ℚ) = 13 ∧
      (91959371382 : ℤ) = ⌊logCenter (9857 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9857 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9857 : Reach 9857 97763653798541 164029719260 := by
  have hr := row_9857
  have hl := log_bounds hr.1
    (by change logScale (9857 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9851) (T := 97671694427159) (U := 164013078322)
    (by norm_num) (by norm_num) hr.1 gap_9857
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9851

theorem gap_9859 : PrimeGap 9857 9859 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9859 :
    (9859 : ℕ).Prime ∧ logScale (9859 : ℚ) = 13 ∧
      (91961400191 : ℤ) = ⌊logCenter (9859 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9859 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9859 : Reach 9859 97855615198732 164046358510 := by
  have hr := row_9859
  have hl := log_bounds hr.1
    (by change logScale (9859 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9857) (T := 97763653798541) (U := 164029719260)
    (by norm_num) (by norm_num) hr.1 gap_9859
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9857

theorem gap_9871 : PrimeGap 9859 9871 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 71, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9871 :
    (9871 : ℕ).Prime ∧ logScale (9871 : ℚ) = 13 ∧
      (91973564410 : ℤ) = ⌊logCenter (9871 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9871 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9871 : Reach 9871 97947588763142 164062979216 := by
  have hr := row_9871
  have hl := log_bounds hr.1
    (by change logScale (9871 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9859) (T := 97855615198732) (U := 164046358510)
    (by norm_num) (by norm_num) hr.1 gap_9871
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9859

theorem gap_9883 : PrimeGap 9871 9883 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9883 :
    (9883 : ℕ).Prime ∧ logScale (9883 : ℚ) = 13 ∧
      (91985713849 : ℤ) = ⌊logCenter (9883 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9883 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9883 : Reach 9883 98039574476991 164079581420 := by
  have hr := row_9883
  have hl := log_bounds hr.1
    (by change logScale (9883 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9871) (T := 97947588763142) (U := 164062979216)
    (by norm_num) (by norm_num) hr.1 gap_9883
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9871

theorem gap_9887 : PrimeGap 9883 9887 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9887 :
    (9887 : ℕ).Prime ∧ logScale (9887 : ℚ) = 13 ∧
      (91989760385 : ℤ) = ⌊logCenter (9887 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9887 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9887 : Reach 9887 98131564237376 164096178586 := by
  have hr := row_9887
  have hl := log_bounds hr.1
    (by change logScale (9887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9883) (T := 98039574476991) (U := 164079581420)
    (by norm_num) (by norm_num) hr.1 gap_9887
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9883

#print axioms reach_9887

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
