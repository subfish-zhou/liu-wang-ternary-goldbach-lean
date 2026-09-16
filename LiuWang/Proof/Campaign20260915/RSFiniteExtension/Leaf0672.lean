import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0671
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15671 : PrimeGap 15667 15671 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15671 :
    (15671 : ℕ).Prime ∧ logScale (15671 : ℚ) = 13 ∧
      (96595671461 : ℤ) = ⌊logCenter (15671 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15671 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15671 : Reach 15671 155676876169189 172231802445 := by
  have hr := row_15671
  have hl := log_bounds hr.1
    (by change logScale (15671 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15667) (T := 155580280497728) (U := 172220811965)
    (by norm_num) (by norm_num) hr.1 gap_15671
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15667

theorem gap_15679 : PrimeGap 15671 15679 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 61, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15679 :
    (15679 : ℕ).Prime ∧ logScale (15679 : ℚ) = 13 ∧
      (96600775129 : ℤ) = ⌊logCenter (15679 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15679 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15679 : Reach 15679 155773476944318 172242788018 := by
  have hr := row_15679
  have hl := log_bounds hr.1
    (by change logScale (15679 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15671) (T := 155676876169189) (U := 172231802445)
    (by norm_num) (by norm_num) hr.1 gap_15679
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15671

theorem gap_15683 : PrimeGap 15679 15683 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15683 :
    (15683 : ℕ).Prime ∧ logScale (15683 : ℚ) = 13 ∧
      (96603325987 : ℤ) = ⌊logCenter (15683 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15683 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15683 : Reach 15683 155870080270305 172253771489 := by
  have hr := row_15683
  have hl := log_bounds hr.1
    (by change logScale (15683 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15679) (T := 155773476944318) (U := 172242788018)
    (by norm_num) (by norm_num) hr.1 gap_15683
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15679

theorem gap_15727 : PrimeGap 15683 15727 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 41, 2, 3, 2, 113, 2, 23, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 79, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15727 :
    (15727 : ℕ).Prime ∧ logScale (15727 : ℚ) = 13 ∧
      (96631342561 : ℤ) = ⌊logCenter (15727 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15727 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15727 : Reach 15727 155966711612866 172264724928 := by
  have hr := row_15727
  have hl := log_bounds hr.1
    (by change logScale (15727 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15683) (T := 155870080270305) (U := 172253771489)
    (by norm_num) (by norm_num) hr.1 gap_15727
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15683

theorem gap_15731 : PrimeGap 15727 15731 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15731 :
    (15731 : ℕ).Prime ∧ logScale (15731 : ℚ) = 13 ∧
      (96633885634 : ℤ) = ⌊logCenter (15731 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15731 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15731 : Reach 15731 156063345498500 172275676278 := by
  have hr := row_15731
  have hl := log_bounds hr.1
    (by change logScale (15731 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15727) (T := 155966711612866) (U := 172264724928)
    (by norm_num) (by norm_num) hr.1 gap_15731
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15727

theorem gap_15733 : PrimeGap 15731 15733 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15733 :
    (15733 : ℕ).Prime ∧ logScale (15733 : ℚ) = 13 ∧
      (96635156928 : ℤ) = ⌊logCenter (15733 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15733 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15733 : Reach 15733 156159980655428 172286626932 := by
  have hr := row_15733
  have hl := log_bounds hr.1
    (by change logScale (15733 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15731) (T := 156063345498500) (U := 172275676278)
    (by norm_num) (by norm_num) hr.1 gap_15733
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15731

theorem gap_15737 : PrimeGap 15733 15737 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15737 :
    (15737 : ℕ).Prime ∧ logScale (15737 : ℚ) = 13 ∧
      (96637699032 : ℤ) = ⌊logCenter (15737 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15737 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15737 : Reach 15737 156256618354460 172297575498 := by
  have hr := row_15737
  have hl := log_bounds hr.1
    (by change logScale (15737 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15733) (T := 156159980655428) (U := 172286626932)
    (by norm_num) (by norm_num) hr.1 gap_15737
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15733

theorem gap_15739 : PrimeGap 15737 15739 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15739 :
    (15739 : ℕ).Prime ∧ logScale (15739 : ℚ) = 13 ∧
      (96638969841 : ℤ) = ⌊logCenter (15739 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15739 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15739 : Reach 15739 156353257324301 172308523368 := by
  have hr := row_15739
  have hl := log_bounds hr.1
    (by change logScale (15739 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15737) (T := 156256618354460) (U := 172297575498)
    (by norm_num) (by norm_num) hr.1 gap_15739
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15737

#print axioms reach_15739

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
