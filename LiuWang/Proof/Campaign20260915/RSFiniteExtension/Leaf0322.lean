import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0321
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7823 : PrimeGap 7817 7823 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7823 :
    (7823 : ℕ).Prime ∧ logScale (7823 : ℚ) = 12 ∧
      (89648233885 : ℤ) = ⌊logCenter (7823 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7823 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7823 : Reach 7823 77135971577230 159862106568 := by
  have hr := row_7823
  have hl := log_bounds hr.1
    (by change logScale (7823 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7817) (T := 77046323343345) (U := 159841671682)
    (by norm_num) (by norm_num) hr.1 gap_7823
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7817

theorem gap_7829 : PrimeGap 7823 7829 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7829 :
    (7829 : ℕ).Prime ∧ logScale (7829 : ℚ) = 12 ∧
      (89655900637 : ℤ) = ⌊logCenter (7829 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7829 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7829 : Reach 7829 77225627477867 159882528401 := by
  have hr := row_7829
  have hl := log_bounds hr.1
    (by change logScale (7829 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7823) (T := 77135971577230) (U := 159862106568)
    (by norm_num) (by norm_num) hr.1 gap_7829
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7823

theorem gap_7841 : PrimeGap 7829 7841 :=
  (primeGap_of_factors (ds := [2, 41, 2, 3, 2, 5, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7841 :
    (7841 : ℕ).Prime ∧ logScale (7841 : ℚ) = 12 ∧
      (89671216531 : ℤ) = ⌊logCenter (7841 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7841 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7841 : Reach 7841 77315298694398 159902921581 := by
  have hr := row_7841
  have hl := log_bounds hr.1
    (by change logScale (7841 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7829) (T := 77225627477867) (U := 159882528401)
    (by norm_num) (by norm_num) hr.1 gap_7841
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7829

theorem gap_7853 : PrimeGap 7841 7853 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 7, 2, 47, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7853 :
    (7853 : ℕ).Prime ∧ logScale (7853 : ℚ) = 12 ∧
      (89686509002 : ℤ) = ⌊logCenter (7853 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7853 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7853 : Reach 7853 77404985203400 159923286192 := by
  have hr := row_7853
  have hl := log_bounds hr.1
    (by change logScale (7853 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7841) (T := 77315298694398) (U := 159902921581)
    (by norm_num) (by norm_num) hr.1 gap_7853
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7841

theorem gap_7867 : PrimeGap 7853 7867 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7867 :
    (7867 : ℕ).Prime ∧ logScale (7867 : ℚ) = 12 ∧
      (89704320712 : ℤ) = ⌊logCenter (7867 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7867 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7867 : Reach 7867 77494689524112 159943617147 := by
  have hr := row_7867
  have hl := log_bounds hr.1
    (by change logScale (7867 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7853) (T := 77404985203400) (U := 159923286192)
    (by norm_num) (by norm_num) hr.1 gap_7867
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7853

theorem gap_7873 : PrimeGap 7867 7873 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7873 :
    (7873 : ℕ).Prime ∧ logScale (7873 : ℚ) = 12 ∧
      (89711944600 : ℤ) = ⌊logCenter (7873 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7873 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7873 : Reach 7873 77584401468712 159963935188 := by
  have hr := row_7873
  have hl := log_bounds hr.1
    (by change logScale (7873 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7867) (T := 77494689524112) (U := 159943617147)
    (by norm_num) (by norm_num) hr.1 gap_7873
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7867

theorem gap_7877 : PrimeGap 7873 7877 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7877 :
    (7877 : ℕ).Prime ∧ logScale (7877 : ℚ) = 12 ∧
      (89717023965 : ℤ) = ⌊logCenter (7877 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7877 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7877 : Reach 7877 77674118492677 159984245490 := by
  have hr := row_7877
  have hl := log_bounds hr.1
    (by change logScale (7877 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7873) (T := 77584401468712) (U := 159963935188)
    (by norm_num) (by norm_num) hr.1 gap_7877
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7873

theorem gap_7879 : PrimeGap 7877 7879 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7879 :
    (7879 : ℕ).Prime ∧ logScale (7879 : ℚ) = 12 ∧
      (89719562681 : ℤ) = ⌊logCenter (7879 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7879 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7879 : Reach 7879 77763838055358 160004553214 := by
  have hr := row_7879
  have hl := log_bounds hr.1
    (by change logScale (7879 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7877) (T := 77674118492677) (U := 159984245490)
    (by norm_num) (by norm_num) hr.1 gap_7879
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7877

#print axioms reach_7879

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
