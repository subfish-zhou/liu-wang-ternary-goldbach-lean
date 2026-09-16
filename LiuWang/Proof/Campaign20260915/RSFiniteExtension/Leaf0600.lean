import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block059
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13913 : PrimeGap 13907 13913 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13913 :
    (13913 : ℕ).Prime ∧ logScale (13913 : ℚ) = 13 ∧
      (95405789304 : ℤ) = ⌊logCenter (13913 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13913 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13913 : Reach 13913 138004855232049 170106705530 := by
  have hr := row_13913
  have hl := log_bounds hr.1
    (by change logScale (13913 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13907) (T := 137909449442745) (U := 170094479072)
    (by norm_num) (by norm_num) hr.1 gap_13913
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13907

theorem gap_13921 : PrimeGap 13913 13921 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13921 :
    (13921 : ℕ).Prime ∧ logScale (13921 : ℚ) = 13 ∧
      (95411537670 : ℤ) = ⌊logCenter (13921 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13921 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13921 : Reach 13921 138100266769719 170118925840 := by
  have hr := row_13921
  have hl := log_bounds hr.1
    (by change logScale (13921 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13913) (T := 138004855232049) (U := 170106705530)
    (by norm_num) (by norm_num) hr.1 gap_13921
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13913

theorem gap_13931 : PrimeGap 13921 13931 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13931 :
    (13931 : ℕ).Prime ∧ logScale (13931 : ℚ) = 13 ∧
      (95418718483 : ℤ) = ⌊logCenter (13931 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13931 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13931 : Reach 13931 138195685488202 170131138254 := by
  have hr := row_13931
  have hl := log_bounds hr.1
    (by change logScale (13931 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13921) (T := 138100266769719) (U := 170118925840)
    (by norm_num) (by norm_num) hr.1 gap_13931
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13921

theorem gap_13933 : PrimeGap 13931 13933 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13933 :
    (13933 : ℕ).Prime ∧ logScale (13933 : ℚ) = 13 ∧
      (95420154027 : ℤ) = ⌊logCenter (13933 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13933 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13933 : Reach 13933 138291105642229 170143349792 := by
  have hr := row_13933
  have hl := log_bounds hr.1
    (by change logScale (13933 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13931) (T := 138195685488202) (U := 170131138254)
    (by norm_num) (by norm_num) hr.1 gap_13933
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13931

theorem gap_13963 : PrimeGap 13933 13963 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 53, 2, 3, 2, 73, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13963 :
    (13963 : ℕ).Prime ∧ logScale (13963 : ℚ) = 13 ∧
      (95441662495 : ℤ) = ⌊logCenter (13963 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13963 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13963 : Reach 13963 138386547304724 170155535966 := by
  have hr := row_13963
  have hl := log_bounds hr.1
    (by change logScale (13963 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13933) (T := 138291105642229) (U := 170143349792)
    (by norm_num) (by norm_num) hr.1 gap_13963
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13933

theorem gap_13967 : PrimeGap 13963 13967 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13967 :
    (13967 : ℕ).Prime ∧ logScale (13967 : ℚ) = 13 ∧
      (95444526799 : ℤ) = ⌊logCenter (13967 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13967 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13967 : Reach 13967 138481991831523 170167719522 := by
  have hr := row_13967
  have hl := log_bounds hr.1
    (by change logScale (13967 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13963) (T := 138386547304724) (U := 170155535966)
    (by norm_num) (by norm_num) hr.1 gap_13967
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13963

theorem gap_13997 : PrimeGap 13967 13997 :=
  (primeGap_of_factors (ds := [2, 61, 2, 3, 2, 89, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 71, 2, 3, 2, 17, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13997 :
    (13997 : ℕ).Prime ∧ logScale (13997 : ℚ) = 13 ∧
      (95465982965 : ℤ) = ⌊logCenter (13997 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13997 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13997 : Reach 13997 138577457814488 170179877833 := by
  have hr := row_13997
  have hl := log_bounds hr.1
    (by change logScale (13997 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13967) (T := 138481991831523) (U := 170167719522)
    (by norm_num) (by norm_num) hr.1 gap_13997
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13967

theorem gap_13999 : PrimeGap 13997 13999 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13999 :
    (13999 : ℕ).Prime ∧ logScale (13999 : ℚ) = 13 ∧
      (95467411740 : ℤ) = ⌊logCenter (13999 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13999 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13999 : Reach 13999 138672925226228 170192035276 := by
  have hr := row_13999
  have hl := log_bounds hr.1
    (by change logScale (13999 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13997) (T := 138577457814488) (U := 170179877833)
    (by norm_num) (by norm_num) hr.1 gap_13999
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13997

#print axioms reach_13999

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
