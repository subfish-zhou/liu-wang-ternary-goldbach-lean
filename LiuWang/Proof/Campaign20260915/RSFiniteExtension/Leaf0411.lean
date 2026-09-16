import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0410
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9697 : PrimeGap 9689 9697 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9697 :
    (9697 : ℕ).Prime ∧ logScale (9697 : ℚ) = 13 ∧
      (91795718349 : ℤ) = ⌊logCenter (9697 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9697 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9697 : Reach 9697 96017796017856 163711542530 := by
  have hr := row_9697
  have hl := log_bounds hr.1
    (by change logScale (9697 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9689) (T := 95926000299507) (U := 163694659829)
    (by norm_num) (by norm_num) hr.1 gap_9697
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9689

theorem gap_9719 : PrimeGap 9697 9719 :=
  (primeGap_of_factors (ds := [2, 3, 2, 89, 2, 31, 2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9719 :
    (9719 : ℕ).Prime ∧ logScale (9719 : ℚ) = 13 ∧
      (91818380081 : ℤ) = ⌊logCenter (9719 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9719 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9719 : Reach 9719 96109614397937 163728388748 := by
  have hr := row_9719
  have hl := log_bounds hr.1
    (by change logScale (9719 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9697) (T := 96017796017856) (U := 163711542530)
    (by norm_num) (by norm_num) hr.1 gap_9719
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9697

theorem gap_9721 : PrimeGap 9719 9721 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9721 :
    (9721 : ℕ).Prime ∧ logScale (9721 : ℚ) = 13 ∧
      (91820437694 : ℤ) = ⌊logCenter (9721 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9721 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9721 : Reach 9721 96201434835631 163745233233 := by
  have hr := row_9721
  have hl := log_bounds hr.1
    (by change logScale (9721 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9719) (T := 96109614397937) (U := 163728388748)
    (by norm_num) (by norm_num) hr.1 gap_9721
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9719

theorem gap_9733 : PrimeGap 9721 9733 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 71, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9733 :
    (9733 : ℕ).Prime ∧ logScale (9733 : ℚ) = 13 ∧
      (91832774490 : ℤ) = ⌊logCenter (9733 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9733 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9733 : Reach 9733 96293267610121 163762058679 := by
  have hr := row_9733
  have hl := log_bounds hr.1
    (by change logScale (9733 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9721) (T := 96201434835631) (U := 163745233233)
    (by norm_num) (by norm_num) hr.1 gap_9733
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9721

theorem gap_9739 : PrimeGap 9733 9739 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9739 :
    (9739 : ℕ).Prime ∧ logScale (9739 : ℚ) = 13 ∧
      (91838937185 : ℤ) = ⌊logCenter (9739 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9739 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9739 : Reach 9739 96385106547306 163778875486 := by
  have hr := row_9739
  have hl := log_bounds hr.1
    (by change logScale (9739 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9733) (T := 96293267610121) (U := 163762058679)
    (by norm_num) (by norm_num) hr.1 gap_9739
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9733

theorem gap_9743 : PrimeGap 9739 9743 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9743 :
    (9743 : ℕ).Prime ∧ logScale (9743 : ℚ) = 13 ∧
      (91843043540 : ℤ) = ⌊logCenter (9743 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9743 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9743 : Reach 9743 96476949590846 163795687114 := by
  have hr := row_9743
  have hl := log_bounds hr.1
    (by change logScale (9743 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9739) (T := 96385106547306) (U := 163778875486)
    (by norm_num) (by norm_num) hr.1 gap_9743
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9739

theorem gap_9749 : PrimeGap 9743 9749 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9749 :
    (9749 : ℕ).Prime ∧ logScale (9749 : ℚ) = 13 ∧
      (91849199912 : ℤ) = ⌊logCenter (9749 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9749 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9749 : Reach 9749 96568798790758 163812490119 := by
  have hr := row_9749
  have hl := log_bounds hr.1
    (by change logScale (9749 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9743) (T := 96476949590846) (U := 163795687114)
    (by norm_num) (by norm_num) hr.1 gap_9749
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9743

theorem gap_9767 : PrimeGap 9749 9767 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 43, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9767 :
    (9767 : ℕ).Prime ∧ logScale (9767 : ℚ) = 13 ∧
      (91867646320 : ℤ) = ⌊logCenter (9767 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9767 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9767 : Reach 9767 96660666437078 163829263874 := by
  have hr := row_9767
  have hl := log_bounds hr.1
    (by change logScale (9767 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9749) (T := 96568798790758) (U := 163812490119)
    (by norm_num) (by norm_num) hr.1 gap_9767
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9749

#print axioms reach_9767

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
