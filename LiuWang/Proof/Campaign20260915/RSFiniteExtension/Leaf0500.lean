import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block049
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11701 : PrimeGap 11699 11701 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11701 :
    (11701 : ℕ).Prime ∧ logScale (11701 : ℚ) = 13 ∧
      (93674295838 : ℤ) = ⌊logCenter (11701 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11701 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11701 : Reach 11701 115309126443209 166940841635 := by
  have hr := row_11701
  have hl := log_bounds hr.1
    (by change logScale (11701 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11699) (T := 115215452147371) (U := 166926574406)
    (by norm_num) (by norm_num) hr.1 gap_11701
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11699

theorem gap_11717 : PrimeGap 11701 11717 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11717 :
    (11717 : ℕ).Prime ∧ logScale (11717 : ℚ) = 13 ∧
      (93687960542 : ℤ) = ⌊logCenter (11717 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11717 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11717 : Reach 11717 115402814403751 166955090598 := by
  have hr := row_11717
  have hl := log_bounds hr.1
    (by change logScale (11717 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11701) (T := 115309126443209) (U := 166940841635)
    (by norm_num) (by norm_num) hr.1 gap_11717
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11701

theorem gap_11719 : PrimeGap 11717 11719 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11719 :
    (11719 : ℕ).Prime ∧ logScale (11719 : ℚ) = 13 ∧
      (93689667318 : ℤ) = ⌊logCenter (11719 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11719 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11719 : Reach 11719 115496504071069 166969338345 := by
  have hr := row_11719
  have hl := log_bounds hr.1
    (by change logScale (11719 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11717) (T := 115402814403751) (U := 166955090598)
    (by norm_num) (by norm_num) hr.1 gap_11719
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11717

theorem gap_11731 : PrimeGap 11719 11731 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 5, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11731 :
    (11731 : ℕ).Prime ∧ logScale (11731 : ℚ) = 13 ∧
      (93699901861 : ℤ) = ⌊logCenter (11731 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11731 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11731 : Reach 11731 115590203972930 166983572731 := by
  have hr := row_11731
  have hl := log_bounds hr.1
    (by change logScale (11731 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11719) (T := 115496504071069) (U := 166969338345)
    (by norm_num) (by norm_num) hr.1 gap_11731
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11719

theorem gap_11743 : PrimeGap 11731 11743 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 59, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11743 :
    (11743 : ℕ).Prime ∧ logScale (11743 : ℚ) = 13 ∧
      (93710125939 : ℤ) = ⌊logCenter (11743 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11743 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11743 : Reach 11743 115683914098869 166997793782 := by
  have hr := row_11743
  have hl := log_bounds hr.1
    (by change logScale (11743 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11731) (T := 115590203972930) (U := 166983572731)
    (by norm_num) (by norm_num) hr.1 gap_11743
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11731

theorem gap_11777 : PrimeGap 11743 11777 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 79, 2, 61, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11777 :
    (11777 : ℕ).Prime ∧ logScale (11777 : ℚ) = 13 ∧
      (93739037524 : ℤ) = ⌊logCenter (11777 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11777 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11777 : Reach 11777 115777653136393 167011974981 := by
  have hr := row_11777
  have hl := log_bounds hr.1
    (by change logScale (11777 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11743) (T := 115683914098869) (U := 166997793782)
    (by norm_num) (by norm_num) hr.1 gap_11777
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11743

theorem gap_11779 : PrimeGap 11777 11779 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11779 :
    (11779 : ℕ).Prime ∧ logScale (11779 : ℚ) = 13 ∧
      (93740735605 : ℤ) = ⌊logCenter (11779 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11779 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11779 : Reach 11779 115871393871998 167026154976 := by
  have hr := row_11779
  have hl := log_bounds hr.1
    (by change logScale (11779 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11777) (T := 115777653136393) (U := 167011974981)
    (by norm_num) (by norm_num) hr.1 gap_11779
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11777

theorem gap_11783 : PrimeGap 11779 11783 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11783 :
    (11783 : ℕ).Prime ∧ logScale (11783 : ℚ) = 13 ∧
      (93744130903 : ℤ) = ⌊logCenter (11783 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11783 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11783 : Reach 11783 115965138002901 167040331360 := by
  have hr := row_11783
  have hl := log_bounds hr.1
    (by change logScale (11783 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11779) (T := 115871393871998) (U := 167026154976)
    (by norm_num) (by norm_num) hr.1 gap_11783
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11779

#print axioms reach_11783

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
