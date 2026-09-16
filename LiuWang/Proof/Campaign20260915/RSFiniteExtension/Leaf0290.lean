import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block028
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7001 : PrimeGap 6997 7001 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7001 :
    (7001 : ℕ).Prime ∧ logScale (7001 : ℚ) = 12 ∧
      (88538082718 : ℤ) = ⌊logCenter (7001 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7001 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7001 : Reach 7001 69292748356929 157977863201 := by
  have hr := row_7001
  have hl := log_bounds hr.1
    (by change logScale (7001 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6997) (T := 69204210274211) (U := 157955298158)
    (by norm_num) (by norm_num) hr.1 gap_7001
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6997

theorem gap_7013 : PrimeGap 7001 7013 :=
  (primeGap_of_factors (ds := [2, 47, 2, 3, 2, 7, 2, 43, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7013 :
    (7013 : ℕ).Prime ∧ logScale (7013 : ℚ) = 12 ∧
      (88555208454 : ℤ) = ⌊logCenter (7013 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7013 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7013 : Reach 7013 69381303565383 158000392845 := by
  have hr := row_7013
  have hl := log_bounds hr.1
    (by change logScale (7013 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7001) (T := 69292748356929) (U := 157977863201)
    (by norm_num) (by norm_num) hr.1 gap_7013
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7001

theorem gap_7019 : PrimeGap 7013 7019 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7019 :
    (7019 : ℕ).Prime ∧ logScale (7019 : ℚ) = 12 ∧
      (88563760336 : ℤ) = ⌊logCenter (7019 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7019 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7019 : Reach 7019 69469867325719 158022906438 := by
  have hr := row_7019
  have hl := log_bounds hr.1
    (by change logScale (7019 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7013) (T := 69381303565383) (U := 158000392845)
    (by norm_num) (by norm_num) hr.1 gap_7019
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7013

theorem gap_7027 : PrimeGap 7019 7027 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7027 :
    (7027 : ℕ).Prime ∧ logScale (7027 : ℚ) = 12 ∧
      (88575151480 : ℤ) = ⌊logCenter (7027 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7027 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7027 : Reach 7027 69558442477199 158045397601 := by
  have hr := row_7027
  have hl := log_bounds hr.1
    (by change logScale (7027 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7019) (T := 69469867325719) (U := 158022906438)
    (by norm_num) (by norm_num) hr.1 gap_7027
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7019

theorem gap_7039 : PrimeGap 7027 7039 :=
  (primeGap_of_factors (ds := [2, 3, 2, 79, 2, 13, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7039 :
    (7039 : ℕ).Prime ∧ logScale (7039 : ℚ) = 12 ∧
      (88592213904 : ℤ) = ⌊logCenter (7039 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7039 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7039 : Reach 7039 69647034691103 158067853611 := by
  have hr := row_7039
  have hl := log_bounds hr.1
    (by change logScale (7039 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7027) (T := 69558442477199) (U := 158045397601)
    (by norm_num) (by norm_num) hr.1 gap_7039
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7027

theorem gap_7043 : PrimeGap 7039 7043 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7043 :
    (7043 : ℕ).Prime ∧ logScale (7043 : ℚ) = 12 ∧
      (88597894916 : ℤ) = ⌊logCenter (7043 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7043 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7043 : Reach 7043 69735632586019 158090300055 := by
  have hr := row_7043
  have hl := log_bounds hr.1
    (by change logScale (7043 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7039) (T := 69647034691103) (U := 158067853611)
    (by norm_num) (by norm_num) hr.1 gap_7043
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7039

theorem gap_7057 : PrimeGap 7043 7057 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7057 :
    (7057 : ℕ).Prime ∧ logScale (7057 : ℚ) = 12 ∧
      (88617753078 : ℤ) = ⌊logCenter (7057 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7057 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7057 : Reach 7057 69824250339097 158112705143 := by
  have hr := row_7057
  have hl := log_bounds hr.1
    (by change logScale (7057 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7043) (T := 69735632586019) (U := 158090300055)
    (by norm_num) (by norm_num) hr.1 gap_7057
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7043

theorem gap_7069 : PrimeGap 7057 7069 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 7, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7069 :
    (7069 : ℕ).Prime ∧ logScale (7069 : ℚ) = 12 ∧
      (88634743030 : ℤ) = ⌊logCenter (7069 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7069 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7069 : Reach 7069 69912885082127 158135075362 := by
  have hr := row_7069
  have hl := log_bounds hr.1
    (by change logScale (7069 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7057) (T := 69824250339097) (U := 158112705143)
    (by norm_num) (by norm_num) hr.1 gap_7069
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7057

#print axioms reach_7069

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
