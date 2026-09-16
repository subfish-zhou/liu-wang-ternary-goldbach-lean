import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block053
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12569 : PrimeGap 12553 12569 :=
  (primeGap_of_factors (ds := [2, 3, 2, 29, 2, 19, 2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12569 :
    (12569 : ℕ).Prime ∧ logScale (12569 : ℚ) = 13 ∧
      (94389887405 : ℤ) = ⌊logCenter (12569 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12569 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12569 : Reach 12569 124337628101360 168265971813 := by
  have hr := row_12569
  have hl := log_bounds hr.1
    (by change logScale (12569 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12553) (T := 124243238213955) (U := 168252584433)
    (by norm_num) (by norm_num) hr.1 gap_12569
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12553

theorem gap_12577 : PrimeGap 12569 12577 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12577 :
    (12577 : ℕ).Prime ∧ logScale (12577 : ℚ) = 13 ∧
      (94396250246 : ℤ) = ⌊logCenter (12577 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12577 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12577 : Reach 12577 124432024351606 168279351741 := by
  have hr := row_12577
  have hl := log_bounds hr.1
    (by change logScale (12577 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12569) (T := 124337628101360) (U := 168265971813)
    (by norm_num) (by norm_num) hr.1 gap_12577
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12569

theorem gap_12583 : PrimeGap 12577 12583 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12583 :
    (12583 : ℕ).Prime ∧ logScale (12583 : ℚ) = 13 ∧
      (94401019722 : ℤ) = ⌊logCenter (12583 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12583 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12583 : Reach 12583 124526425371328 168292726352 := by
  have hr := row_12583
  have hl := log_bounds hr.1
    (by change logScale (12583 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12577) (T := 124432024351606) (U := 168279351741)
    (by norm_num) (by norm_num) hr.1 gap_12583
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12577

theorem gap_12589 : PrimeGap 12583 12589 :=
  (primeGap_of_factors (ds := [2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12589 :
    (12589 : ℕ).Prime ∧ logScale (12589 : ℚ) = 13 ∧
      (94405786923 : ℤ) = ⌊logCenter (12589 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12589 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12589 : Reach 12589 124620831158251 168306095651 := by
  have hr := row_12589
  have hl := log_bounds hr.1
    (by change logScale (12589 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12583) (T := 124526425371328) (U := 168292726352)
    (by norm_num) (by norm_num) hr.1 gap_12589
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12583

theorem gap_12601 : PrimeGap 12589 12601 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12601 :
    (12601 : ℕ).Prime ∧ logScale (12601 : ℚ) = 13 ∧
      (94415314514 : ℤ) = ⌊logCenter (12601 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12601 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12601 : Reach 12601 124715246472765 168319453278 := by
  have hr := row_12601
  have hl := log_bounds hr.1
    (by change logScale (12601 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12589) (T := 124620831158251) (U := 168306095651)
    (by norm_num) (by norm_num) hr.1 gap_12601
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12589

theorem gap_12611 : PrimeGap 12601 12611 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12611 :
    (12611 : ℕ).Prime ∧ logScale (12611 : ℚ) = 13 ∧
      (94423247245 : ℤ) = ⌊logCenter (12611 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12611 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12611 : Reach 12611 124809669720010 168332801372 := by
  have hr := row_12611
  have hl := log_bounds hr.1
    (by change logScale (12611 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12601) (T := 124715246472765) (U := 168319453278)
    (by norm_num) (by norm_num) hr.1 gap_12611
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12601

theorem gap_12613 : PrimeGap 12611 12613 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12613 :
    (12613 : ℕ).Prime ∧ logScale (12613 : ℚ) = 13 ∧
      (94424833037 : ℤ) = ⌊logCenter (12613 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12613 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12613 : Reach 12613 124904094553047 168346148407 := by
  have hr := row_12613
  have hl := log_bounds hr.1
    (by change logScale (12613 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12611) (T := 124809669720010) (U := 168332801372)
    (by norm_num) (by norm_num) hr.1 gap_12613
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12611

theorem gap_12619 : PrimeGap 12613 12619 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12619 :
    (12619 : ℕ).Prime ∧ logScale (12619 : ℚ) = 13 ∧
      (94429588902 : ℤ) = ⌊logCenter (12619 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12619 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12619 : Reach 12619 124998524141949 168359490153 := by
  have hr := row_12619
  have hl := log_bounds hr.1
    (by change logScale (12619 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12613) (T := 124904094553047) (U := 168346148407)
    (by norm_num) (by norm_num) hr.1 gap_12619
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12613

#print axioms reach_12619

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
