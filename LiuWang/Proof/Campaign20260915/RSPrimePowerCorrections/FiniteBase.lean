import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.Raw
import LiuWang.Proof.Campaign20260915.Totient.ThetaLogData
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open Finset
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections

def thetaUpperUnits (n : ℕ) : ℤ :=
  thetaInteger n + 61 * (n + 1)

def higherUpperUnits (n : ℕ) : ℤ :=
  ∑ k ∈ Icc 3 17, thetaUpperUnits (Nat.nthRoot k n)

private theorem log_row_lookup :
    ∀ p ∈ range 257, 0 ≤ unitsFrom thetaLogRows p ∧
      (p.Prime → ∃ r ∈ thetaLogRows.toFinset,
        r.1 = p ∧ unitsFrom thetaLogRows p = r.2 ∧ logScale (p : ℚ) ≤ 10) := by
  decide +kernel

theorem theta_upper_pilot :
    ∀ n ∈ Icc 1 16, thetaUpperUnits n < 10000000000 * (n : ℤ) := by
  decide +kernel

theorem higher_upper_pilot :
    ∀ n ∈ Icc 1 4, higherUpperUnits ((n + 1) ^ 3) < 30000000000 * (n : ℤ) := by
  decide +kernel

noncomputable section

theorem theta_le_upper_units {n : ℕ} (hn : n ≤ 256) :
    Chebyshev.theta n ≤ (thetaUpperUnits n : ℝ) / 10000000000 := by
  have hterm (p : ℕ) (hp : p ∈ range (n + 1)) :
      (if p.Prime then Real.log p else 0) ≤
        ((unitsFrom thetaLogRows p : ℝ) + 61) / 10000000000 := by
    have hp257 : p ∈ range 257 := by
      simp only [mem_range] at hp ⊢
      omega
    have hrow := log_row_lookup p hp257
    split_ifs with hprime
    · obtain ⟨r, hr, hrp, hru, hrs⟩ := hrow.2 hprime
      have hchecked := theta_log_rows_checked r (List.mem_toFinset.mp hr)
      have hu : unitsFrom thetaLogRows p = ⌊logCenter (p : ℚ) * 10000000000⌋ := by
        rw [hru, hchecked.2, hrp]
      have h := (rational_log_bounds (x := (p : ℚ))
        (by exact_mod_cast hprime.one_le)).2
      unfold logHi logLo at h
      rw [← hu] at h
      push_cast at h
      have hs : (logScale (p : ℚ) : ℝ) ≤ 10 := by exact_mod_cast hrs
      linarith
    · have hu : (0 : ℝ) ≤ unitsFrom thetaLogRows p := by exact_mod_cast hrow.1
      positivity
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  change (∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p) ≤ _
  rw [sum_filter]
  have h := sum_le_sum hterm
  unfold thetaUpperUnits thetaInteger
  push_cast
  simpa only [← sum_div, sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_comm (61 : ℝ)] using h

theorem floor_root_eq_nthRoot (n : ℕ) {k : ℕ} (hk : 0 < k) :
    ⌊(n : ℝ) ^ (1 / (k : ℝ))⌋₊ = Nat.nthRoot k n := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg n) _)).mpr
    rw [one_div, Real.rpow_inv_lt_iff_of_pos (by positivity) (by positivity) hkR,
      Real.rpow_natCast]
    exact_mod_cast Nat.lt_pow_nthRoot_add_one hk.ne' n
  · apply Nat.le_floor
    rw [one_div, Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hkR,
      Real.rpow_natCast]
    exact_mod_cast Nat.pow_nthRoot_le (n := k) (a := n) (Or.inl hk.ne')

theorem theta_root_eq_nthRoot (n : ℕ) {k : ℕ} (hk : 0 < k) :
    Chebyshev.theta ((n : ℝ) ^ (1 / (k : ℝ))) =
      Chebyshev.theta (Nat.nthRoot k n) := by
  rw [Chebyshev.theta_eq_theta_coe_floor, floor_root_eq_nthRoot n hk]

theorem higherPrimePowers_nat_le_upper_units {n : ℕ} (hn : 0 < n)
    (hnB : n ≤ 68921) :
    higherPrimePowers n ≤ (higherUpperUnits n : ℝ) / 10000000000 := by
  have hcut : ⌊Real.log (n : ℝ) / Real.log 2⌋₊ ≤ 17 :=
    log_cutoff_of_lt_pow_two (by exact_mod_cast hn) (by
      have h : (n : ℝ) ≤ 68921 := by exact_mod_cast hnB
      norm_num
      linarith)
  rw [higherPrimePowers_eq_sum (Nat.cast_nonneg n) (by norm_num : 2 ≤ 17) hcut]
  unfold higherUpperUnits
  push_cast
  rw [sum_div]
  apply sum_le_sum
  intro k hk
  have hk3 := (mem_Icc.mp hk).1
  rw [theta_root_eq_nthRoot n (by omega)]
  apply theta_le_upper_units
  apply Nat.le_of_lt_succ
  rw [Nat.nthRoot_lt_iff (by omega : k ≠ 0)]
  change n < 257 ^ k
  have hpow : (257 : ℕ) ^ 3 ≤ 257 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  norm_num at hpow
  omega

#print axioms theta_le_upper_units
#print axioms floor_root_eq_nthRoot
#print axioms higherPrimePowers_nat_le_upper_units
#print axioms theta_upper_pilot
#print axioms higher_upper_pilot

end
end LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections
