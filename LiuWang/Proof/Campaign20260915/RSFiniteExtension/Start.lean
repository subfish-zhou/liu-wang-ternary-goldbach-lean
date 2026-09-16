import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Core

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem state_1420 : State 1420 13455622264421 129402528355 := by
  constructor
  · have he : thetaInteger 1420 = 13455622264421 := by
      rw [thetaInteger_eq_prefixUnits]
      decide +kernel
    simpa only [he] using thetaInteger_le_theta 1420
  · have he : eulerUnits 1420 = 129402528355 :=
      (productWalk_sound (by norm_num : 0 < (287 : ℕ))
        eulerUnits_286 product_walk_all).1
    simpa only [he] using prefixEuler_le_units 1420

theorem gap_1420_1423 : PrimeGap 1420 1423 := by decide +kernel

theorem row_1423 :
    (1423 : ℕ).Prime ∧ logScale (1423 : ℚ) = 10 ∧
      (72605225954 : ℤ) = ⌊logCenter (1423 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1423 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1423 : Reach 1423 13528227490375 129493528727 := by
  have hr := row_1423
  have hl := log_bounds hr.1
    (by change logScale (1423 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  have hs : State 1423 13528227490375 129493528727 :=
    state_next (a := 1420) (T := 13455622264421) (U := 129402528355)
      (by norm_num) hr.1 gap_1420_1423 hl.1 (by norm_num) state_1420
  have hprod : (prefixEuler 1423 : ℝ) < productEnvelope 1423 := by
    have hn : (129493528727 : ℚ) / 10000000000 < lowerEnvelope 72605225954 := by
      norm_num [lowerEnvelope]
    have hnR := Rat.cast_lt (K := ℝ) |>.mpr hn
    push_cast at hnR
    exact hs.2.trans_lt (hnR.trans_le (lowerEnvelope_le (by norm_num) hl.1 hl.2))
  refine ⟨hs, ?_, ?_⟩
  · intro x hx hi
    by_cases he : x = 1423
    · subst x
      simpa using hprod
    exact product_between (by norm_num : 3 ≤ (1420 : ℕ)) gap_1420_1423 hx
      (lt_of_le_of_ne hi he) (product_3_29_nat (by norm_num) le_rfl)
  · intro x hx hi
    have he : x = 1423 := le_antisymm hi hx
    subst x
    exact theta_endpoint (b := 1423) (by norm_num) le_rfl (by norm_num) hs.1

theorem theta_gt_sub_two_sqrt_upto_1420_9 {x : ℝ}
    (hx : 0 < x) (hi : x ≤ 1420.9) :
    x - 2 * Real.sqrt x < Chebyshev.theta x := by
  by_cases hs : x ≤ 1420
  · exact theta_gt_sub_two_sqrt_upto_1420 hx hs
  apply theta_endpoint (T := 13455622264421) (b := 1420.9) (by linarith) hi
  · norm_num
  · exact state_1420.1.trans
      (Chebyshev.theta_mono (by norm_num only [Nat.cast_ofNat]; exact le_of_not_ge hs))

theorem complete_start :
    ∀ p ∈ Finset.Ioc 1420 1423, p.Prime ↔ p ∈ ([1423] : List ℕ) := by
  decide +kernel

#print axioms reach_1423
#print axioms theta_gt_sub_two_sqrt_upto_1420_9

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
