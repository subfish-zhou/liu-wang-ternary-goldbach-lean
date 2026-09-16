import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0411
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9769 : PrimeGap 9767 9769 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9769 :
    (9769 : ℕ).Prime ∧ logScale (9769 : ℚ) = 13 ∧
      (91869693822 : ℤ) = ⌊logCenter (9769 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9769 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9769 : Reach 9769 96752536130900 163846035912 := by
  have hr := row_9769
  have hl := log_bounds hr.1
    (by change logScale (9769 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9767) (T := 96660666437078) (U := 163829263874)
    (by norm_num) (by norm_num) hr.1 gap_9769
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9767

theorem gap_9781 : PrimeGap 9769 9781 :=
  (primeGap_of_factors (ds := [2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9781 :
    (9781 : ℕ).Prime ∧ logScale (9781 : ℚ) = 13 ∧
      (91881970039 : ℤ) = ⌊logCenter (9781 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9781 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9781 : Reach 9781 96844418100939 163862789086 := by
  have hr := row_9781
  have hl := log_bounds hr.1
    (by change logScale (9781 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9769) (T := 96752536130900) (U := 163846035912)
    (by norm_num) (by norm_num) hr.1 gap_9781
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9769

theorem gap_9787 : PrimeGap 9781 9787 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9787 :
    (9787 : ℕ).Prime ∧ logScale (9787 : ℚ) = 13 ∧
      (91888102500 : ℤ) = ⌊logCenter (9787 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9787 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9787 : Reach 9787 96936306203439 163879533700 := by
  have hr := row_9787
  have hl := log_bounds hr.1
    (by change logScale (9787 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9781) (T := 96844418100939) (U := 163862789086)
    (by norm_num) (by norm_num) hr.1 gap_9787
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9781

theorem gap_9791 : PrimeGap 9787 9791 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9791 :
    (9791 : ℕ).Prime ∧ logScale (9791 : ℚ) = 13 ∧
      (91892188719 : ℤ) = ⌊logCenter (9791 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9791 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9791 : Reach 9791 97028198392158 163896273183 := by
  have hr := row_9791
  have hl := log_bounds hr.1
    (by change logScale (9791 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9787) (T := 96936306203439) (U := 163879533700)
    (by norm_num) (by norm_num) hr.1 gap_9791
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9787

theorem gap_9803 : PrimeGap 9791 9803 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 97, 2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9803 :
    (9803 : ℕ).Prime ∧ logScale (9803 : ℚ) = 13 ∧
      (91904437368 : ℤ) = ⌊logCenter (9803 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9803 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9803 : Reach 9803 97120102829526 163912993881 := by
  have hr := row_9803
  have hl := log_bounds hr.1
    (by change logScale (9803 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9791) (T := 97028198392158) (U := 163896273183)
    (by norm_num) (by norm_num) hr.1 gap_9803
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9791

theorem gap_9811 : PrimeGap 9803 9811 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9811 :
    (9811 : ℕ).Prime ∧ logScale (9811 : ℚ) = 13 ∧
      (91912594807 : ℤ) = ⌊logCenter (9811 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9811 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9811 : Reach 9811 97212015424333 163929702647 := by
  have hr := row_9811
  have hl := log_bounds hr.1
    (by change logScale (9811 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9803) (T := 97120102829526) (U := 163912993881)
    (by norm_num) (by norm_num) hr.1 gap_9811
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9803

theorem gap_9817 : PrimeGap 9811 9817 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9817 :
    (9817 : ℕ).Prime ∧ logScale (9817 : ℚ) = 13 ∧
      (91918708523 : ℤ) = ⌊logCenter (9817 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9817 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9817 : Reach 9817 97303934132856 163946402902 := by
  have hr := row_9817
  have hl := log_bounds hr.1
    (by change logScale (9817 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9811) (T := 97212015424333) (U := 163929702647)
    (by norm_num) (by norm_num) hr.1 gap_9817
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9811

theorem gap_9829 : PrimeGap 9817 9829 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 11, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9829 :
    (9829 : ℕ).Prime ∧ logScale (9829 : ℚ) = 13 ∧
      (91930924751 : ℤ) = ⌊logCenter (9829 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9829 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9829 : Reach 9829 97395865057607 163963084466 := by
  have hr := row_9829
  have hl := log_bounds hr.1
    (by change logScale (9829 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9817) (T := 97303934132856) (U := 163946402902)
    (by norm_num) (by norm_num) hr.1 gap_9829
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9817

#print axioms reach_9829

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
