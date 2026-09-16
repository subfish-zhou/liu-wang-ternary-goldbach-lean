import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0611
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14387 : PrimeGap 14369 14387 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 73, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14387 :
    (14387 : ℕ).Prime ∧ logScale (14387 : ℚ) = 13 ∧
      (95740802966 : ℤ) = ⌊logCenter (14387 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14387 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14387 : Reach 14387 141827785113787 170588362246 := by
  have hr := row_14387
  have hl := log_bounds hr.1
    (by change logScale (14387 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14369) (T := 141732044310821) (U := 170576505127)
    (by norm_num) (by norm_num) hr.1 gap_14387
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14369

theorem gap_14389 : PrimeGap 14387 14389 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14389 :
    (14389 : ℕ).Prime ∧ logScale (14389 : ℚ) = 13 ∧
      (95742193013 : ℤ) = ⌊logCenter (14389 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14389 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14389 : Reach 14389 141923527306800 170600218541 := by
  have hr := row_14389
  have hl := log_bounds hr.1
    (by change logScale (14389 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14387) (T := 141827785113787) (U := 170588362246)
    (by norm_num) (by norm_num) hr.1 gap_14389
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14387

theorem gap_14401 : PrimeGap 14389 14401 :=
  (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14401 :
    (14401 : ℕ).Prime ∧ logScale (14401 : ℚ) = 13 ∧
      (95750529242 : ℤ) = ⌊logCenter (14401 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14401 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14401 : Reach 14401 142019277836042 170612065779 := by
  have hr := row_14401
  have hl := log_bounds hr.1
    (by change logScale (14401 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14389) (T := 141923527306800) (U := 170600218541)
    (by norm_num) (by norm_num) hr.1 gap_14401
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14389

theorem gap_14407 : PrimeGap 14401 14407 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14407 :
    (14407 : ℕ).Prime ∧ logScale (14407 : ℚ) = 13 ∧
      (95754694751 : ℤ) = ⌊logCenter (14407 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14407 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14407 : Reach 14407 142115032530793 170623908905 := by
  have hr := row_14407
  have hl := log_bounds hr.1
    (by change logScale (14407 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14401) (T := 142019277836042) (U := 170612065779)
    (by norm_num) (by norm_num) hr.1 gap_14407
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14401

theorem gap_14411 : PrimeGap 14407 14411 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14411 :
    (14411 : ℕ).Prime ∧ logScale (14411 : ℚ) = 13 ∧
      (95757470794 : ℤ) = ⌊logCenter (14411 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14411 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14411 : Reach 14411 142210790001587 170635749565 := by
  have hr := row_14411
  have hl := log_bounds hr.1
    (by change logScale (14411 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14407) (T := 142115032530793) (U := 170623908905)
    (by norm_num) (by norm_num) hr.1 gap_14411
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14407

theorem gap_14419 : PrimeGap 14411 14419 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14419 :
    (14419 : ℕ).Prime ∧ logScale (14419 : ℚ) = 13 ∧
      (95763020569 : ℤ) = ⌊logCenter (14419 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14419 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14419 : Reach 14419 142306553022156 170647584477 := by
  have hr := row_14419
  have hl := log_bounds hr.1
    (by change logScale (14419 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14411) (T := 142210790001587) (U := 170635749565)
    (by norm_num) (by norm_num) hr.1 gap_14419
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14411

theorem gap_14423 : PrimeGap 14419 14423 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14423 :
    (14423 : ℕ).Prime ∧ logScale (14423 : ℚ) = 13 ∧
      (95765794302 : ℤ) = ⌊logCenter (14423 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14423 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14423 : Reach 14423 142402318816458 170659416927 := by
  have hr := row_14423
  have hl := log_bounds hr.1
    (by change logScale (14423 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14419) (T := 142306553022156) (U := 170647584477)
    (by norm_num) (by norm_num) hr.1 gap_14423
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14419

theorem gap_14431 : PrimeGap 14423 14431 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 47, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14431 :
    (14431 : ℕ).Prime ∧ logScale (14431 : ℚ) = 13 ∧
      (95771339460 : ℤ) = ⌊logCenter (14431 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14431 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14431 : Reach 14431 142498090155918 170671243637 := by
  have hr := row_14431
  have hl := log_bounds hr.1
    (by change logScale (14431 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14423) (T := 142402318816458) (U := 170659416927)
    (by norm_num) (by norm_num) hr.1 gap_14431
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14423

#print axioms reach_14431

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
