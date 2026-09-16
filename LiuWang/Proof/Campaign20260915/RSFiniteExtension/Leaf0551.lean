import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0550
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12889 : PrimeGap 12853 12889 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 17, 2, 61, 2, 3, 2, 5, 2, 79, 2, 3, 2, 11, 2, 13, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12889 :
    (12889 : ℕ).Prime ∧ logScale (12889 : ℚ) = 13 ∧
      (94641295100 : ℤ) = ⌊logCenter (12889 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12889 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12889 : Reach 12889 127361778131055 168690038600 := by
  have hr := row_12889
  have hl := log_bounds hr.1
    (by change logScale (12889 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12853) (T := 127267136835955) (U := 168676950692)
    (by norm_num) (by norm_num) hr.1 gap_12889
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12853

theorem gap_12893 : PrimeGap 12889 12893 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12893 :
    (12893 : ℕ).Prime ∧ logScale (12893 : ℚ) = 13 ∧
      (94644398040 : ℤ) = ⌊logCenter (12893 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12893 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12893 : Reach 12893 127456422529095 168703123462 := by
  have hr := row_12893
  have hl := log_bounds hr.1
    (by change logScale (12893 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12889) (T := 127361778131055) (U := 168690038600)
    (by norm_num) (by norm_num) hr.1 gap_12893
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12889

theorem gap_12899 : PrimeGap 12893 12899 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12899 :
    (12899 : ℕ).Prime ∧ logScale (12899 : ℚ) = 13 ∧
      (94649050645 : ℤ) = ⌊logCenter (12899 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12899 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12899 : Reach 12899 127551071579740 168716203252 := by
  have hr := row_12899
  have hl := log_bounds hr.1
    (by change logScale (12899 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12893) (T := 127456422529095) (U := 168703123462)
    (by norm_num) (by norm_num) hr.1 gap_12899
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12893

theorem gap_12907 : PrimeGap 12899 12907 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12907 :
    (12907 : ℕ).Prime ∧ logScale (12907 : ℚ) = 13 ∧
      (94655250754 : ℤ) = ⌊logCenter (12907 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12907 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12907 : Reach 12907 127645726830494 168729275948 := by
  have hr := row_12907
  have hl := log_bounds hr.1
    (by change logScale (12907 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12899) (T := 127551071579740) (U := 168716203252)
    (by norm_num) (by norm_num) hr.1 gap_12907
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12899

theorem gap_12911 : PrimeGap 12907 12911 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12911 :
    (12911 : ℕ).Prime ∧ logScale (12911 : ℚ) = 13 ∧
      (94658349367 : ℤ) = ⌊logCenter (12911 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12911 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12911 : Reach 12911 127740385179861 168742345606 := by
  have hr := row_12911
  have hl := log_bounds hr.1
    (by change logScale (12911 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12907) (T := 127645726830494) (U := 168729275948)
    (by norm_num) (by norm_num) hr.1 gap_12911
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12907

theorem gap_12917 : PrimeGap 12911 12917 :=
  (primeGap_of_factors (ds := [2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12917 :
    (12917 : ℕ).Prime ∧ logScale (12917 : ℚ) = 13 ∧
      (94662995488 : ℤ) = ⌊logCenter (12917 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12917 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12917 : Reach 12917 127835048175349 168755410204 := by
  have hr := row_12917
  have hl := log_bounds hr.1
    (by change logScale (12917 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12911) (T := 127740385179861) (U := 168742345606)
    (by norm_num) (by norm_num) hr.1 gap_12917
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12911

theorem gap_12919 : PrimeGap 12917 12919 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12919 :
    (12919 : ℕ).Prime ∧ logScale (12919 : ℚ) = 13 ∧
      (94664543715 : ℤ) = ⌊logCenter (12919 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12919 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12919 : Reach 12919 127929712719064 168768473791 := by
  have hr := row_12919
  have hl := log_bounds hr.1
    (by change logScale (12919 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12917) (T := 127835048175349) (U := 168755410204)
    (by norm_num) (by norm_num) hr.1 gap_12919
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12917

theorem gap_12923 : PrimeGap 12919 12923 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12923 :
    (12923 : ℕ).Prime ∧ logScale (12923 : ℚ) = 13 ∧
      (94667639451 : ℤ) = ⌊logCenter (12923 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12923 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12923 : Reach 12923 128024380358515 168781534345 := by
  have hr := row_12923
  have hl := log_bounds hr.1
    (by change logScale (12923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12919) (T := 127929712719064) (U := 168768473791)
    (by norm_num) (by norm_num) hr.1 gap_12923
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12919

#print axioms reach_12923

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
