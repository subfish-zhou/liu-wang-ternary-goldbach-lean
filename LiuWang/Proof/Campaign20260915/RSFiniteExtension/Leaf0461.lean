import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0460
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10837 : PrimeGap 10831 10837 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10837 :
    (10837 : ℕ).Prime ∧ logScale (10837 : ℚ) = 13 ∧
      (92907214805 : ℤ) = ⌊logCenter (10837 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10837 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10837 : Reach 10837 107099791741280 165640570374 := by
  have hr := row_10837
  have hl := log_bounds hr.1
    (by change logScale (10837 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10831) (T := 107006884526475) (U := 165625285648)
    (by norm_num) (by norm_num) hr.1 gap_10837
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10831

theorem gap_10847 : PrimeGap 10837 10847 :=
  (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10847 :
    (10847 : ℕ).Prime ∧ logScale (10847 : ℚ) = 13 ∧
      (92916438196 : ℤ) = ⌊logCenter (10847 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10847 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10847 : Reach 10847 107192708179476 165655842417 := by
  have hr := row_10847
  have hl := log_bounds hr.1
    (by change logScale (10847 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10837) (T := 107099791741280) (U := 165640570374)
    (by norm_num) (by norm_num) hr.1 gap_10847
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10837

theorem gap_10853 : PrimeGap 10847 10853 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10853 :
    (10853 : ℕ).Prime ∧ logScale (10853 : ℚ) = 13 ∧
      (92921968150 : ℤ) = ⌊logCenter (10853 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10853 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10853 : Reach 10853 107285630147626 165671107423 := by
  have hr := row_10853
  have hl := log_bounds hr.1
    (by change logScale (10853 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10847) (T := 107192708179476) (U := 165655842417)
    (by norm_num) (by norm_num) hr.1 gap_10853
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10847

theorem gap_10859 : PrimeGap 10853 10859 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10859 :
    (10859 : ℕ).Prime ∧ logScale (10859 : ℚ) = 13 ∧
      (92927495048 : ℤ) = ⌊logCenter (10859 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10859 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10859 : Reach 10859 107378557642674 165686365400 := by
  have hr := row_10859
  have hl := log_bounds hr.1
    (by change logScale (10859 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10853) (T := 107285630147626) (U := 165671107423)
    (by norm_num) (by norm_num) hr.1 gap_10859
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10853

theorem gap_10861 : PrimeGap 10859 10861 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10861 :
    (10861 : ℕ).Prime ∧ logScale (10861 : ℚ) = 13 ∧
      (92929336669 : ℤ) = ⌊logCenter (10861 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10861 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10861 : Reach 10861 107471486979343 165701621972 := by
  have hr := row_10861
  have hl := log_bounds hr.1
    (by change logScale (10861 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10859) (T := 107378557642674) (U := 165686365400)
    (by norm_num) (by norm_num) hr.1 gap_10861
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10859

theorem gap_10867 : PrimeGap 10861 10867 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10867 :
    (10867 : ℕ).Prime ∧ logScale (10867 : ℚ) = 13 ∧
      (92934859496 : ℤ) = ⌊logCenter (10867 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10867 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10867 : Reach 10867 107564421838839 165716871524 := by
  have hr := row_10867
  have hl := log_bounds hr.1
    (by change logScale (10867 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10861) (T := 107471486979343) (U := 165701621972)
    (by norm_num) (by norm_num) hr.1 gap_10867
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10861

theorem gap_10883 : PrimeGap 10867 10883 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 83, 2, 3, 2, 73, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10883 :
    (10883 : ℕ).Prime ∧ logScale (10883 : ℚ) = 13 ∧
      (92949572143 : ℤ) = ⌊logCenter (10883 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10883 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10883 : Reach 10883 107657371410982 165732100055 := by
  have hr := row_10883
  have hl := log_bounds hr.1
    (by change logScale (10883 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10867) (T := 107564421838839) (U := 165716871524)
    (by norm_num) (by norm_num) hr.1 gap_10883
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10867

theorem gap_10889 : PrimeGap 10883 10889 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10889 :
    (10889 : ℕ).Prime ∧ logScale (10889 : ℚ) = 13 ∧
      (92955083809 : ℤ) = ⌊logCenter (10889 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10889 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10889 : Reach 10889 107750326494791 165747321593 := by
  have hr := row_10889
  have hl := log_bounds hr.1
    (by change logScale (10889 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10883) (T := 107657371410982) (U := 165732100055)
    (by norm_num) (by norm_num) hr.1 gap_10889
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10883

#print axioms reach_10889

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
