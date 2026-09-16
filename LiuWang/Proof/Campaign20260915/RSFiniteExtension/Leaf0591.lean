import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0590
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13763 : PrimeGap 13759 13763 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13763 :
    (13763 : ℕ).Prime ∧ logScale (13763 : ℚ) = 13 ∧
      (95297391076 : ℤ) = ⌊logCenter (13763 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13763 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13763 : Reach 13763 136479037539623 169910360621 := by
  have hr := row_13763
  have hl := log_bounds hr.1
    (by change logScale (13763 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13759) (T := 136383740148547) (U := 169898015175)
    (by norm_num) (by norm_num) hr.1 gap_13763
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13759

theorem gap_13781 : PrimeGap 13763 13781 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5, 2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13781 :
    (13781 : ℕ).Prime ∧ logScale (13781 : ℚ) = 13 ∧
      (95310461074 : ℤ) = ⌊logCenter (13781 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13781 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13781 : Reach 13781 136574348000697 169922690836 := by
  have hr := row_13781
  have hl := log_bounds hr.1
    (by change logScale (13781 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13763) (T := 136479037539623) (U := 169910360621)
    (by norm_num) (by norm_num) hr.1 gap_13781
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13763

theorem gap_13789 : PrimeGap 13781 13789 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13789 :
    (13789 : ℕ).Prime ∧ logScale (13789 : ℚ) = 13 ∧
      (95316264484 : ℤ) = ⌊logCenter (13789 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13789 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13789 : Reach 13789 136669664265181 169935014791 := by
  have hr := row_13789
  have hl := log_bounds hr.1
    (by change logScale (13789 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13781) (T := 136574348000697) (U := 169922690836)
    (by norm_num) (by norm_num) hr.1 gap_13789
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13781

theorem gap_13799 : PrimeGap 13789 13799 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13799 :
    (13799 : ℕ).Prime ∧ logScale (13799 : ℚ) = 13 ∧
      (95323514013 : ℤ) = ⌊logCenter (13799 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13799 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13799 : Reach 13799 136764987779194 169947330708 := by
  have hr := row_13799
  have hl := log_bounds hr.1
    (by change logScale (13799 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13789) (T := 136669664265181) (U := 169935014791)
    (by norm_num) (by norm_num) hr.1 gap_13799
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13789

theorem gap_13807 : PrimeGap 13799 13807 :=
  (primeGap_of_factors (ds := [2, 37, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13807 :
    (13807 : ℕ).Prime ∧ logScale (13807 : ℚ) = 13 ∧
      (95329309855 : ℤ) = ⌊logCenter (13807 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13807 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13807 : Reach 13807 136860317089049 169959640380 := by
  have hr := row_13807
  have hl := log_bounds hr.1
    (by change logScale (13807 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13799) (T := 136764987779194) (U := 169947330708)
    (by norm_num) (by norm_num) hr.1 gap_13807
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13799

theorem gap_13829 : PrimeGap 13807 13829 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 19, 2, 3, 2, 41, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13829 :
    (13829 : ℕ).Prime ∧ logScale (13829 : ℚ) = 13 ∧
      (95345231120 : ℤ) = ⌊logCenter (13829 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13829 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13829 : Reach 13829 136955662320169 169971931358 := by
  have hr := row_13829
  have hl := log_bounds hr.1
    (by change logScale (13829 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13807) (T := 136860317089049) (U := 169959640380)
    (by norm_num) (by norm_num) hr.1 gap_13829
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13807

theorem gap_13831 : PrimeGap 13829 13831 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13831 :
    (13831 : ℕ).Prime ∧ logScale (13831 : ℚ) = 13 ∧
      (95346677252 : ℤ) = ⌊logCenter (13831 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13831 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13831 : Reach 13831 137051008997421 169984221448 := by
  have hr := row_13831
  have hl := log_bounds hr.1
    (by change logScale (13831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13829) (T := 136955662320169) (U := 169971931358)
    (by norm_num) (by norm_num) hr.1 gap_13831
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13829

theorem gap_13841 : PrimeGap 13831 13841 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 101, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13841 :
    (13841 : ℕ).Prime ∧ logScale (13841 : ℚ) = 13 ∧
      (95353904775 : ℤ) = ⌊logCenter (13841 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13841 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13841 : Reach 13841 137146362902196 169996503545 := by
  have hr := row_13841
  have hl := log_bounds hr.1
    (by change logScale (13841 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13831) (T := 137051008997421) (U := 169984221448)
    (by norm_num) (by norm_num) hr.1 gap_13841
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13831

#print axioms reach_13841

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
