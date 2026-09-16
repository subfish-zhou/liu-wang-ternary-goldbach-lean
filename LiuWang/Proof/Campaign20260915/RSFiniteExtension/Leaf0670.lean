import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block066
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15541 : PrimeGap 15527 15541 :=
  (primeGap_of_factors (ds := [2, 53, 2, 3, 2, 7, 2, 5, 2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15541 :
    (15541 : ℕ).Prime ∧ logScale (15541 : ℚ) = 13 ∧
      (96512369685 : ℤ) = ⌊logCenter (15541 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15541 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15541 : Reach 15541 154131894354949 172055434612 := by
  have hr := row_15541
  have hl := log_bounds hr.1
    (by change logScale (15541 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15527) (T := 154035381985264) (U := 172044363546)
    (by norm_num) (by norm_num) hr.1 gap_15541
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15527

theorem gap_15551 : PrimeGap 15541 15551 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15551 :
    (15551 : ℕ).Prime ∧ logScale (15551 : ℚ) = 13 ∧
      (96518802208 : ℤ) = ⌊logCenter (15551 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15551 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15551 : Reach 15551 154228413157157 172066499271 := by
  have hr := row_15551
  have hl := log_bounds hr.1
    (by change logScale (15551 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15541) (T := 154131894354949) (U := 172055434612)
    (by norm_num) (by norm_num) hr.1 gap_15551
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15541

theorem gap_15559 : PrimeGap 15551 15559 :=
  (primeGap_of_factors (ds := [2, 103, 2, 3, 2, 47, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15559 :
    (15559 : ℕ).Prime ∧ logScale (15559 : ℚ) = 13 ∧
      (96523945249 : ℤ) = ⌊logCenter (15559 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15559 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15559 : Reach 15559 154324937102406 172077558951 := by
  have hr := row_15559
  have hl := log_bounds hr.1
    (by change logScale (15559 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15551) (T := 154228413157157) (U := 172066499271)
    (by norm_num) (by norm_num) hr.1 gap_15559
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15551

theorem gap_15569 : PrimeGap 15559 15569 :=
  (primeGap_of_factors (ds := [2, 3, 2, 79, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15569 :
    (15569 : ℕ).Prime ∧ logScale (15569 : ℚ) = 13 ∧
      (96530370333 : ℤ) = ⌊logCenter (15569 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15569 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15569 : Reach 15569 154421467472739 172088612238 := by
  have hr := row_15569
  have hl := log_bounds hr.1
    (by change logScale (15569 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15559) (T := 154324937102406) (U := 172077558951)
    (by norm_num) (by norm_num) hr.1 gap_15569
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15559

theorem gap_15581 : PrimeGap 15569 15581 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 5, 2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15581 :
    (15581 : ℕ).Prime ∧ logScale (15581 : ℚ) = 13 ∧
      (96538074988 : ℤ) = ⌊logCenter (15581 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15581 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15581 : Reach 15581 154518005547727 172099657721 := by
  have hr := row_15581
  have hl := log_bounds hr.1
    (by change logScale (15581 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15569) (T := 154421467472739) (U := 172088612238)
    (by norm_num) (by norm_num) hr.1 gap_15581
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15569

theorem gap_15583 : PrimeGap 15581 15583 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15583 :
    (15583 : ℕ).Prime ∧ logScale (15583 : ℚ) = 13 ∧
      (96539358520 : ℤ) = ⌊logCenter (15583 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15583 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15583 : Reach 15583 154614544906247 172110702495 := by
  have hr := row_15583
  have hl := log_bounds hr.1
    (by change logScale (15583 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15581) (T := 154518005547727) (U := 172099657721)
    (by norm_num) (by norm_num) hr.1 gap_15583
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15581

theorem gap_15601 : PrimeGap 15583 15601 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15601 :
    (15601 : ℕ).Prime ∧ logScale (15601 : ℚ) = 13 ∧
      (96550902903 : ℤ) = ⌊logCenter (15601 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15601 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15601 : Reach 15601 154711095809150 172121735233 := by
  have hr := row_15601
  have hl := log_bounds hr.1
    (by change logScale (15601 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15583) (T := 154614544906247) (U := 172110702495)
    (by norm_num) (by norm_num) hr.1 gap_15601
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15583

theorem gap_15607 : PrimeGap 15601 15607 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15607 :
    (15607 : ℕ).Prime ∧ logScale (15607 : ℚ) = 13 ∧
      (96554748071 : ℤ) = ⌊logCenter (15607 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15607 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15607 : Reach 15607 154807650557221 172132764436 := by
  have hr := row_15607
  have hl := log_bounds hr.1
    (by change logScale (15607 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15601) (T := 154711095809150) (U := 172121735233)
    (by norm_num) (by norm_num) hr.1 gap_15607
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15601

#print axioms reach_15607

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
