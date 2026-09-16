import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0270
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_6679 : PrimeGap 6673 6679 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6679 :
    (6679 : ℕ).Prime ∧ logScale (6679 : ℚ) = 12 ∧
      (88067235516 : ℤ) = ⌊logCenter (6679 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6679 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6679 : Reach 6679 65760007818958 157057752789 := by
  have hr := row_6679
  have hl := log_bounds hr.1
    (by change logScale (6679 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6673) (T := 65671940583442) (U := 157034237629)
    (by norm_num) (by norm_num) hr.1 gap_6679
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6673

theorem gap_6689 : PrimeGap 6679 6689 :=
  (primeGap_of_factors (ds := [2, 3, 2, 41, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6689 :
    (6689 : ℕ).Prime ∧ logScale (6689 : ℚ) = 12 ∧
      (88082196619 : ℤ) = ⌊logCenter (6689 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6689 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6689 : Reach 6689 65848090015577 157081236305 := by
  have hr := row_6689
  have hl := log_bounds hr.1
    (by change logScale (6689 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6679) (T := 65760007818958) (U := 157057752789)
    (by norm_num) (by norm_num) hr.1 gap_6689
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6679

theorem gap_6691 : PrimeGap 6689 6691 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6691 :
    (6691 : ℕ).Prime ∧ logScale (6691 : ℚ) = 12 ∧
      (88085186156 : ℤ) = ⌊logCenter (6691 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6691 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6691 : Reach 6691 65936175201733 157104716311 := by
  have hr := row_6691
  have hl := log_bounds hr.1
    (by change logScale (6691 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6689) (T := 65848090015577) (U := 157081236305)
    (by norm_num) (by norm_num) hr.1 gap_6691
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6689

theorem gap_6701 : PrimeGap 6691 6701 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6701 :
    (6701 : ℕ).Prime ∧ logScale (6701 : ℚ) = 12 ∧
      (88100120448 : ℤ) = ⌊logCenter (6701 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6701 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6701 : Reach 6701 66024275322181 157128164777 := by
  have hr := row_6701
  have hl := log_bounds hr.1
    (by change logScale (6701 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6691) (T := 65936175201733) (U := 157104716311)
    (by norm_num) (by norm_num) hr.1 gap_6701
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6691

theorem gap_6703 : PrimeGap 6701 6703 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6703 :
    (6703 : ℕ).Prime ∧ logScale (6703 : ℚ) = 12 ∧
      (88103104632 : ℤ) = ⌊logCenter (6703 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6703 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6703 : Reach 6703 66112378426813 157151609744 := by
  have hr := row_6703
  have hl := log_bounds hr.1
    (by change logScale (6703 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6701) (T := 66024275322181) (U := 157128164777)
    (by norm_num) (by norm_num) hr.1 gap_6703
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6701

theorem gap_6709 : PrimeGap 6703 6709 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6709 :
    (6709 : ℕ).Prime ∧ logScale (6709 : ℚ) = 12 ∧
      (88112051844 : ℤ) = ⌊logCenter (6709 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6709 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6709 : Reach 6709 66200490478657 157175037236 := by
  have hr := row_6709
  have hl := log_bounds hr.1
    (by change logScale (6709 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6703) (T := 66112378426813) (U := 157151609744)
    (by norm_num) (by norm_num) hr.1 gap_6709
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6703

theorem gap_6719 : PrimeGap 6709 6719 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6719 :
    (6719 : ℕ).Prime ∧ logScale (6719 : ℚ) = 12 ∧
      (88126946098 : ℤ) = ⌊logCenter (6719 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6719 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6719 : Reach 6719 66288617424755 157198433342 := by
  have hr := row_6719
  have hl := log_bounds hr.1
    (by change logScale (6719 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6709) (T := 66200490478657) (U := 157175037236)
    (by norm_num) (by norm_num) hr.1 gap_6719
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6709

theorem gap_6733 : PrimeGap 6719 6733 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6733 :
    (6733 : ℕ).Prime ∧ logScale (6733 : ℚ) = 12 ∧
      (88147760854 : ℤ) = ⌊logCenter (6733 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6733 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6733 : Reach 6733 66376765185609 157221784268 := by
  have hr := row_6733
  have hl := log_bounds hr.1
    (by change logScale (6733 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6719) (T := 66288617424755) (U := 157198433342)
    (by norm_num) (by norm_num) hr.1 gap_6733
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6719

#print axioms reach_6733

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
