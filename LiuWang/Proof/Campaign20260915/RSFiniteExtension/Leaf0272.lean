import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0271
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_6737 : PrimeGap 6733 6737 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6737 :
    (6737 : ℕ).Prime ∧ logScale (6737 : ℚ) = 12 ∧
      (88153699978 : ℤ) = ⌊logCenter (6737 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6737 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6737 : Reach 6737 66464918885587 157245124795 := by
  have hr := row_6737
  have hl := log_bounds hr.1
    (by change logScale (6737 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6733) (T := 66376765185609) (U := 157221784268)
    (by norm_num) (by norm_num) hr.1 gap_6737
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6733

theorem gap_6761 : PrimeGap 6737 6761 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 43, 2, 3, 2, 5, 2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6761 :
    (6761 : ℕ).Prime ∧ logScale (6761 : ℚ) = 12 ∧
      (88189260839 : ℤ) = ⌊logCenter (6761 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6761 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6761 : Reach 6761 66553108146426 157268385909 := by
  have hr := row_6761
  have hl := log_bounds hr.1
    (by change logScale (6761 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6737) (T := 66464918885587) (U := 157245124795)
    (by norm_num) (by norm_num) hr.1 gap_6761
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6737

theorem gap_6763 : PrimeGap 6761 6763 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6763 :
    (6763 : ℕ).Prime ∧ logScale (6763 : ℚ) = 12 ∧
      (88192218544 : ℤ) = ⌊logCenter (6763 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6763 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6763 : Reach 6763 66641300364970 157291643583 := by
  have hr := row_6763
  have hl := log_bounds hr.1
    (by change logScale (6763 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6761) (T := 66553108146426) (U := 157268385909)
    (by norm_num) (by norm_num) hr.1 gap_6763
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6761

theorem gap_6779 : PrimeGap 6763 6779 :=
  (primeGap_of_factors (ds := [2, 3, 2, 67, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6779 :
    (6779 : ℕ).Prime ∧ logScale (6779 : ℚ) = 12 ∧
      (88215848743 : ℤ) = ⌊logCenter (6779 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6779 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6779 : Reach 6779 66729516213713 157314849786 := by
  have hr := row_6779
  have hl := log_bounds hr.1
    (by change logScale (6779 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6763) (T := 66641300364970) (U := 157291643583)
    (by norm_num) (by norm_num) hr.1 gap_6779
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6763

theorem gap_6781 : PrimeGap 6779 6781 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6781 :
    (6781 : ℕ).Prime ∧ logScale (6781 : ℚ) = 12 ∧
      (88218798595 : ℤ) = ⌊logCenter (6781 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6781 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6781 : Reach 6781 66817735012308 157338052567 := by
  have hr := row_6781
  have hl := log_bounds hr.1
    (by change logScale (6781 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6779) (T := 66729516213713) (U := 157314849786)
    (by norm_num) (by norm_num) hr.1 gap_6781
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6779

theorem gap_6791 : PrimeGap 6781 6791 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6791 :
    (6791 : ℕ).Prime ∧ logScale (6791 : ℚ) = 12 ∧
      (88233534819 : ℤ) = ⌊logCenter (6791 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6791 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6791 : Reach 6791 66905968547127 157361224593 := by
  have hr := row_6791
  have hl := log_bounds hr.1
    (by change logScale (6791 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6781) (T := 66817735012308) (U := 157338052567)
    (by norm_num) (by norm_num) hr.1 gap_6791
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6781

theorem gap_6793 : PrimeGap 6791 6793 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6793 :
    (6793 : ℕ).Prime ∧ logScale (6793 : ℚ) = 12 ∧
      (88236479460 : ℤ) = ⌊logCenter (6793 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6793 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6793 : Reach 6793 66994205026587 157384393207 := by
  have hr := row_6793
  have hl := log_bounds hr.1
    (by change logScale (6793 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6791) (T := 66905968547127) (U := 157361224593)
    (by norm_num) (by norm_num) hr.1 gap_6793
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6791

theorem gap_6803 : PrimeGap 6793 6803 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6803 :
    (6803 : ℕ).Prime ∧ logScale (6803 : ℚ) = 12 ∧
      (88251189672 : ℤ) = ⌊logCenter (6803 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6803 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6803 : Reach 6803 67082456216259 157407531166 := by
  have hr := row_6803
  have hl := log_bounds hr.1
    (by change logScale (6803 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6793) (T := 66994205026587) (U := 157384393207)
    (by norm_num) (by norm_num) hr.1 gap_6803
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6793

#print axioms reach_6803

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
