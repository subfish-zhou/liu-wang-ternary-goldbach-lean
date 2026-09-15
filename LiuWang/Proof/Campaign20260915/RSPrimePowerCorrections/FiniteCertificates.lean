import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.FiniteBase

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open Finset

namespace LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections

private theorem theta_upper_block_1 :
    ∀ n ∈ Icc 1 64, thetaUpperUnits n < 10000000000 * (n : ℤ) := by
  decide +kernel

private theorem theta_upper_block_2 :
    ∀ n ∈ Icc 65 128, thetaUpperUnits n < 10000000000 * (n : ℤ) := by
  decide +kernel

private theorem theta_upper_block_3 :
    ∀ n ∈ Icc 129 192, thetaUpperUnits n < 10000000000 * (n : ℤ) := by
  decide +kernel

private theorem theta_upper_block_4 :
    ∀ n ∈ Icc 193 256, thetaUpperUnits n < 10000000000 * (n : ℤ) := by
  decide +kernel

theorem theta_upper_certificate {n : ℕ} (hn1 : 1 ≤ n) (hn256 : n ≤ 256) :
    thetaUpperUnits n < 10000000000 * (n : ℤ) := by
  by_cases h1 : n ≤ 64
  · exact theta_upper_block_1 n (mem_Icc.mpr ⟨hn1, h1⟩)
  by_cases h2 : n ≤ 128
  · exact theta_upper_block_2 n (mem_Icc.mpr ⟨by omega, h2⟩)
  by_cases h3 : n ≤ 192
  · exact theta_upper_block_3 n (mem_Icc.mpr ⟨by omega, h3⟩)
  exact theta_upper_block_4 n (mem_Icc.mpr ⟨by omega, hn256⟩)

private theorem higher_upper_block_1 :
    ∀ n ∈ Icc 1 10, higherUpperUnits ((n + 1) ^ 3) < 30000000000 * (n : ℤ) := by
  decide +kernel

private theorem higher_upper_block_2 :
    ∀ n ∈ Icc 11 20, higherUpperUnits ((n + 1) ^ 3) < 30000000000 * (n : ℤ) := by
  decide +kernel

private theorem higher_upper_block_3 :
    ∀ n ∈ Icc 21 30, higherUpperUnits ((n + 1) ^ 3) < 30000000000 * (n : ℤ) := by
  decide +kernel

private theorem higher_upper_block_4 :
    ∀ n ∈ Icc 31 40, higherUpperUnits ((n + 1) ^ 3) < 30000000000 * (n : ℤ) := by
  decide +kernel

theorem higher_upper_certificate {n : ℕ} (hn1 : 1 ≤ n) (hn40 : n ≤ 40) :
    higherUpperUnits ((n + 1) ^ 3) < 30000000000 * (n : ℤ) := by
  by_cases h1 : n ≤ 10
  · exact higher_upper_block_1 n (mem_Icc.mpr ⟨hn1, h1⟩)
  by_cases h2 : n ≤ 20
  · exact higher_upper_block_2 n (mem_Icc.mpr ⟨by omega, h2⟩)
  by_cases h3 : n ≤ 30
  · exact higher_upper_block_3 n (mem_Icc.mpr ⟨by omega, h3⟩)
  exact higher_upper_block_4 n (mem_Icc.mpr ⟨by omega, hn40⟩)

noncomputable section

theorem theta_lt_self_up_to_256 {y : ℝ} (hy : 0 < y) (hy256 : y ≤ 256) :
    Chebyshev.theta y < y := by
  by_cases hy1 : y < 1
  · rw [Chebyshev.theta_eq_zero_of_le_one hy1.le]
    exact hy
  have hn1 : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff y).mpr (le_of_not_gt hy1)
  have hn256 : ⌊y⌋₊ ≤ 256 := by
    have h := Nat.floor_le_floor hy256
    norm_num at h
    exact h
  have hcert : (thetaUpperUnits ⌊y⌋₊ : ℝ) < 10000000000 * (⌊y⌋₊ : ℝ) := by
    exact_mod_cast theta_upper_certificate hn1 hn256
  rw [Chebyshev.theta_eq_theta_coe_floor]
  apply (theta_le_upper_units hn256).trans_lt
  apply lt_of_lt_of_le _ (Nat.floor_le hy.le)
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 10000000000)).mpr
  linarith

theorem theta_le_self_up_to_256 {y : ℝ} (hy : 0 ≤ y) (hy256 : y ≤ 256) :
    Chebyshev.theta y ≤ y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp
  exact (theta_lt_self_up_to_256 hy hy256).le

theorem higherPrimePowers_lt_three_small {x : ℝ} (hx : 0 < x) (hxB : x < 65536) :
    higherPrimePowers x < 3 * x ^ (1 / (3 : ℝ)) := by
  by_cases hx8 : x < 8
  · have hcut : ⌊Real.log x / Real.log 2⌋₊ ≤ 2 :=
      log_cutoff_of_lt_pow_two hx (by norm_num; exact hx8)
    rw [higherPrimePowers_eq_sum hx.le (by norm_num : 2 ≤ 2) hcut]
    norm_num
    positivity
  let n := ⌊x ^ (1 / (3 : ℝ))⌋₊
  have hr0 : 0 ≤ x ^ (1 / (3 : ℝ)) := Real.rpow_nonneg hx.le _
  have hn1 : 1 ≤ n := by
    apply (Nat.one_le_floor_iff _).mpr
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hn40 : n ≤ 40 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt hr0).mpr
    change x ^ (1 / (3 : ℝ)) < (41 : ℝ)
    rw [one_div, Real.rpow_inv_lt_iff_of_pos hx.le (by norm_num) (by norm_num)]
    norm_num
    linarith
  have hxnext : x ≤ (((n + 1) ^ 3 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (x ^ (1 / (3 : ℝ)))
    change x ^ (1 / (3 : ℝ)) < (n : ℝ) + 1 at h
    rw [one_div, Real.rpow_inv_lt_iff_of_pos hx.le (by positivity) (by norm_num)] at h
    norm_num at h
    exact_mod_cast h.le
  have hnext : (n + 1) ^ 3 ≤ 68921 := by
    have := Nat.pow_le_pow_left (show n + 1 ≤ 41 by omega) 3
    norm_num at this
    exact this
  have hnum : (higherUpperUnits ((n + 1) ^ 3) : ℝ) < 30000000000 * (n : ℝ) := by
    exact_mod_cast higher_upper_certificate hn1 hn40
  have hfloor : (n : ℝ) ≤ x ^ (1 / (3 : ℝ)) := Nat.floor_le hr0
  calc
    higherPrimePowers x ≤ higherPrimePowers (((n + 1) ^ 3 : ℕ) : ℝ) :=
      higherPrimePowers_mono hx.le hxnext
    _ ≤ (higherUpperUnits ((n + 1) ^ 3) : ℝ) / 10000000000 :=
      higherPrimePowers_nat_le_upper_units (by positivity) hnext
    _ < 3 * (n : ℝ) := by
      apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 10000000000)).mpr
      linarith
    _ ≤ _ := by linarith

#print axioms theta_upper_certificate
#print axioms higher_upper_certificate
#print axioms theta_lt_self_up_to_256
#print axioms higherPrimePowers_lt_three_small

end
end LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections
