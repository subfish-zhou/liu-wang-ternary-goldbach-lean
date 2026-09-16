import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block067
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15749 : PrimeGap 15739 15749 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15749 :
    (15749 : ℕ).Prime ∧ logScale (15749 : ℚ) = 13 ∧
      (96645321467 : ℤ) = ⌊logCenter (15749 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15749 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15749 : Reach 15749 156449902645768 172319464982 := by
  have hr := row_15749
  have hl := log_bounds hr.1
    (by change logScale (15749 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15739) (T := 156353257324301) (U := 172308523368)
    (by norm_num) (by norm_num) hr.1 gap_15749
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15739

theorem gap_15761 : PrimeGap 15749 15761 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15761 :
    (15761 : ℕ).Prime ∧ logScale (15761 : ℚ) = 13 ∧
      (96652938097 : ℤ) = ⌊logCenter (15761 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15761 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15761 : Reach 15761 156546555583865 172330398959 := by
  have hr := row_15761
  have hl := log_bounds hr.1
    (by change logScale (15761 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15749) (T := 156449902645768) (U := 172319464982)
    (by norm_num) (by norm_num) hr.1 gap_15761
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15749

theorem gap_15767 : PrimeGap 15761 15767 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15767 :
    (15767 : ℕ).Prime ∧ logScale (15767 : ℚ) = 13 ∧
      (96656744238 : ℤ) = ⌊logCenter (15767 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15767 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15767 : Reach 15767 156643212328103 172341329468 := by
  have hr := row_15767
  have hl := log_bounds hr.1
    (by change logScale (15767 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15761) (T := 156546555583865) (U := 172330398959)
    (by norm_num) (by norm_num) hr.1 gap_15767
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15761

theorem gap_15773 : PrimeGap 15767 15773 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15773 :
    (15773 : ℕ).Prime ∧ logScale (15773 : ℚ) = 13 ∧
      (96660548931 : ℤ) = ⌊logCenter (15773 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15773 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15773 : Reach 15773 156739872877034 172352256512 := by
  have hr := row_15773
  have hl := log_bounds hr.1
    (by change logScale (15773 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15767) (T := 156643212328103) (U := 172341329468)
    (by norm_num) (by norm_num) hr.1 gap_15773
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15767

theorem gap_15787 : PrimeGap 15773 15787 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 31, 2, 43, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15787 :
    (15787 : ℕ).Prime ∧ logScale (15787 : ℚ) = 13 ∧
      (96669420921 : ℤ) = ⌊logCenter (15787 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15787 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15787 : Reach 15787 156836542297955 172363174557 := by
  have hr := row_15787
  have hl := log_bounds hr.1
    (by change logScale (15787 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15773) (T := 156739872877034) (U := 172352256512)
    (by norm_num) (by norm_num) hr.1 gap_15787
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15773

theorem gap_15791 : PrimeGap 15787 15791 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15791 :
    (15791 : ℕ).Prime ∧ logScale (15791 : ℚ) = 13 ∧
      (96671954330 : ℤ) = ⌊logCenter (15791 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15791 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15791 : Reach 15791 156933214252285 172374090528 := by
  have hr := row_15791
  have hl := log_bounds hr.1
    (by change logScale (15791 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15787) (T := 156836542297955) (U := 172363174557)
    (by norm_num) (by norm_num) hr.1 gap_15791
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15787

theorem gap_15797 : PrimeGap 15791 15797 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15797 :
    (15797 : ℕ).Prime ∧ logScale (15797 : ℚ) = 13 ∧
      (96675753241 : ℤ) = ⌊logCenter (15797 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15797 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15797 : Reach 15797 157029890005526 172385003044 := by
  have hr := row_15797
  have hl := log_bounds hr.1
    (by change logScale (15797 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15791) (T := 156933214252285) (U := 172374090528)
    (by norm_num) (by norm_num) hr.1 gap_15797
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15791

theorem gap_15803 : PrimeGap 15797 15803 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15803 :
    (15803 : ℕ).Prime ∧ logScale (15803 : ℚ) = 13 ∧
      (96679550710 : ℤ) = ⌊logCenter (15803 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15803 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15803 : Reach 15803 157126569556236 172395912107 := by
  have hr := row_15803
  have hl := log_bounds hr.1
    (by change logScale (15803 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15797) (T := 157029890005526) (U := 172385003044)
    (by norm_num) (by norm_num) hr.1 gap_15803
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15797

#print axioms reach_15803

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
