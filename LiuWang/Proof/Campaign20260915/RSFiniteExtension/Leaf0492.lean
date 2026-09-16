import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0491
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11617 : PrimeGap 11597 11617 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11617 :
    (11617 : ℕ).Prime ∧ logScale (11617 : ℚ) = 13 ∧
      (93602248181 : ℤ) = ⌊logCenter (11617 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11617 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11617 : Reach 11617 114559946249753 166826431815 := by
  have hr := row_11617
  have hl := log_bounds hr.1
    (by change logScale (11617 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11597) (T := 114466344001572) (U := 166812071271)
    (by norm_num) (by norm_num) hr.1 gap_11617
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11597

theorem gap_11621 : PrimeGap 11617 11621 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11621 :
    (11621 : ℕ).Prime ∧ logScale (11621 : ℚ) = 13 ∧
      (93605690818 : ℤ) = ⌊logCenter (11621 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11621 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11621 : Reach 11621 114653551940571 166840788651 := by
  have hr := row_11621
  have hl := log_bounds hr.1
    (by change logScale (11621 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11617) (T := 114559946249753) (U := 166826431815)
    (by norm_num) (by norm_num) hr.1 gap_11621
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11617

theorem gap_11633 : PrimeGap 11621 11633 :=
  (primeGap_of_factors (ds := [2, 59, 2, 3, 2, 7, 2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11633 :
    (11633 : ℕ).Prime ∧ logScale (11633 : ℚ) = 13 ∧
      (93616011624 : ℤ) = ⌊logCenter (11633 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11633 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11633 : Reach 11633 114747167952195 166855131910 := by
  have hr := row_11633
  have hl := log_bounds hr.1
    (by change logScale (11633 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11621) (T := 114653551940571) (U := 166840788651)
    (by norm_num) (by norm_num) hr.1 gap_11633
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11621

theorem gap_11657 : PrimeGap 11633 11657 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 103, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 61, 2, 43, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11657 :
    (11657 : ℕ).Prime ∧ logScale (11657 : ℚ) = 13 ∧
      (93636621335 : ℤ) = ⌊logCenter (11657 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11657 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11657 : Reach 11657 114840804573530 166869446867 := by
  have hr := row_11657
  have hl := log_bounds hr.1
    (by change logScale (11657 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11633) (T := 114747167952195) (U := 166855131910)
    (by norm_num) (by norm_num) hr.1 gap_11657
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11633

theorem gap_11677 : PrimeGap 11657 11677 :=
  (primeGap_of_factors (ds := [2, 89, 2, 3, 2, 107, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11677 :
    (11677 : ℕ).Prime ∧ logScale (11677 : ℚ) = 13 ∧
      (93653763706 : ℤ) = ⌊logCenter (11677 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11677 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11677 : Reach 11677 114934458337236 166883738530 := by
  have hr := row_11677
  have hl := log_bounds hr.1
    (by change logScale (11677 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11657) (T := 114840804573530) (U := 166869446867)
    (by norm_num) (by norm_num) hr.1 gap_11677
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11657

theorem gap_11681 : PrimeGap 11677 11681 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11681 :
    (11681 : ℕ).Prime ∧ logScale (11681 : ℚ) = 13 ∧
      (93657188657 : ℤ) = ⌊logCenter (11681 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11681 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11681 : Reach 11681 115028115525893 166898026522 := by
  have hr := row_11681
  have hl := log_bounds hr.1
    (by change logScale (11681 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11677) (T := 114934458337236) (U := 166883738530)
    (by norm_num) (by norm_num) hr.1 gap_11681
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11677

theorem gap_11689 : PrimeGap 11681 11689 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11689 :
    (11689 : ℕ).Prime ∧ logScale (11689 : ℚ) = 13 ∧
      (93664035042 : ℤ) = ⌊logCenter (11689 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11689 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11689 : Reach 11689 115121779560935 166912305957 := by
  have hr := row_11689
  have hl := log_bounds hr.1
    (by change logScale (11689 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11681) (T := 115028115525893) (U := 166898026522)
    (by norm_num) (by norm_num) hr.1 gap_11689
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11681

theorem gap_11699 : PrimeGap 11689 11699 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11699 :
    (11699 : ℕ).Prime ∧ logScale (11699 : ℚ) = 13 ∧
      (93672586436 : ℤ) = ⌊logCenter (11699 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11699 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11699 : Reach 11699 115215452147371 166926574406 := by
  have hr := row_11699
  have hl := log_bounds hr.1
    (by change logScale (11699 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11689) (T := 115121779560935) (U := 166912305957)
    (by norm_num) (by norm_num) hr.1 gap_11699
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11689

#print axioms reach_11699

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
