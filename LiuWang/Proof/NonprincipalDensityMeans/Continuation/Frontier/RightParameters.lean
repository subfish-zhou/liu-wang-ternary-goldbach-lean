import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.DetectorEnergy

/-! # Explicit harmonic and Abel costs at N = ceil(q y), M = N squared -/

set_option autoImplicit false
noncomputable section

open Finset
open MathlibNt.SieveTheory.LiuWeight
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

theorem ceil_parameters (q : ℕ) [NeZero q] {y : ℝ} (hy : 2 ≤ y) :
    2 ≤ ⌈(q : ℝ) * y⌉₊ ∧ q ≤ ⌈(q : ℝ) * y⌉₊ ∧
      (q : ℝ) * y ≤ ⌈(q : ℝ) * y⌉₊ ∧
      (⌈(q : ℝ) * y⌉₊ : ℝ) ≤ 2 * ((q : ℝ) * y) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hz : 2 ≤ (q : ℝ) * y := by nlinarith
  have hN := Nat.le_ceil ((q : ℝ) * y)
  have hupper := Nat.ceil_lt_add_one (show 0 ≤ (q : ℝ) * y by positivity)
  refine ⟨Nat.ofNat_le_cast.mp (hz.trans hN), (Nat.cast_le (α := ℝ)).mp ?_, hN, ?_⟩
  · exact (le_mul_of_one_le_right (by positivity) (by linarith)).trans hN
  · linarith

theorem right_log_N {z : ℝ} (hz : 2 ≤ z) {N : ℕ} (hN : 2 ≤ N)
    (hNz : (N : ℝ) ≤ 2 * z) :
    1 ≤ 1 + Real.log z ∧ Real.log (N : ℝ) ≤ 1 + Real.log z := by
  have hz0 : 0 < z := by linarith
  have hlog := Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hNz
  rw [Real.log_mul (by norm_num) hz0.ne'] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  exact ⟨by linarith [Real.log_nonneg (show 1 ≤ z by linarith)], by linarith⟩

theorem right_harmonics (q N : ℕ) {z : ℝ} (hz : 2 ≤ z)
    (hN : 2 ≤ N) (hNz : (N : ℝ) ≤ 2 * z) :
    liuHarmonic (N ^ 2 * N) ≤ 4 * (1 + Real.log z) ∧
      harmonicRange ((N ^ 2 * N + 1) / q + 1) ≤ 5 * (1 + Real.log z) ∧
      harmonicRange (N / q + 1) ≤ 3 * (1 + Real.log z) ∧
      harmonicRange N ≤ 2 * (1 + Real.log z) := by
  have hL := right_log_N hz hN hNz
  have hn : (2 : ℝ) ≤ N := Nat.ofNat_le_cast.mpr hN
  have hnp : (0 : ℝ) < N := by linarith
  have htwo : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hc : Real.log (N ^ 2 * N : ℕ) = 3 * Real.log (N : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (pow_ne_zero _ hnp.ne') hnp.ne',
      Real.log_pow]
    ring
  have hbig : Real.log ((N ^ 2 * N + 1) / q + 1 : ℕ) ≤
      1 + 3 * Real.log (N : ℝ) := by
    have ha : (((N ^ 2 * N + 1) / q + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ 3 := by
      have hd : ((N ^ 2 * N + 1) / q + 1 : ℕ) ≤ N ^ 2 * N + 2 :=
        Nat.add_le_add_right (Nat.div_le_self _ _) 1
      have hd' := (Nat.cast_le (α := ℝ)).mpr hd
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hd'
      have : (2 : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 2)]
      push_cast
      nlinarith
    have hl := Real.log_le_log (by positivity) ha
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hnp.ne'), Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have hsmall : Real.log (N / q + 1 : ℕ) ≤ 1 + Real.log (N : ℝ) := by
    have ha : ((N / q + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      have hd := (Nat.cast_le (α := ℝ)).mpr (Nat.div_le_self N q)
      push_cast
      linarith
    have hl := Real.log_le_log (by positivity) ha
    rw [Real.log_mul (by norm_num) hnp.ne'] at hl
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := liuHarmonic_le_one_add_log (N ^ 2 * N)
    rw [hc] at h
    linarith
  · have h := inverse_range_le_log ((N ^ 2 * N + 1) / q + 1)
    change harmonicRange _ ≤ _ at h
    linarith
  · have h := inverse_range_le_log (N / q + 1)
    change harmonicRange _ ≤ _ at h
    linarith
  · have h := inverse_range_le_log N
    change harmonicRange _ ≤ _ at h
    linarith

theorem right_mollifier_cost (q : ℕ) [NeZero q] {y : ℝ} (hy : 2 ≤ y) :
    mollifierMeanBound q ((q : ℝ) * y) y ≤
      52 * y * (1 + Real.log ((q : ℝ) * y)) ^ 2 := by
  let N := ⌈(q : ℝ) * y⌉₊
  have hp := ceil_parameters q hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hz : 2 ≤ (q : ℝ) * y := by nlinarith
  have hh := right_harmonics q N hz hp.1 hp.2.2.2
  have hL := (right_log_N hz hp.1 hp.2.2.2).1
  have hNq : (N : ℝ) / q ≤ 2 * y := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < q)).mpr
    nlinarith only [hp.2.2.2]
  have hfac : meanFactor q N y ≤ 26 * y * (1 + Real.log ((q : ℝ) * y)) := by
    have hm := mul_le_mul hNq hh.2.2.1 (harmonicRange_nonneg _)
      (by positivity : 0 ≤ 2 * y)
    unfold meanFactor logRowBound
    change 2 * y + 2 * (2 * (N : ℝ) / q * harmonicRange (N / q + 1)) ≤ _
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith [mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ 1 + Real.log ((q : ℝ) * y) - 1 by linarith)]
  have hm := mul_le_mul hfac hh.2.2.2 (harmonicRange_nonneg _)
    (by positivity : 0 ≤ 26 * y * (1 + Real.log ((q : ℝ) * y)))
  exact hm.trans_eq (by ring)

theorem right_error_cost (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : 1 ≤ sigma) :
    stripError q (⌈(q : ℝ) * y⌉₊ ^ 2) sigma y ^ 2 ≤
      16 / ((q : ℝ) * y) := by
  let N := ⌈(q : ℝ) * y⌉₊
  have hp := ceil_parameters q hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hn : (2 : ℝ) ≤ N := Nat.ofNat_le_cast.mpr hp.1
  have hn0 : (0 : ℝ) < N := by linarith
  have hy0 : 0 < y := by linarith
  have hq0 : (0 : ℝ) < q := by positivity
  have he : ((N ^ 2 : ℕ) : ℝ) ^ (-2 * sigma) ≤ ((N : ℝ) ^ 4)⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ (N ^ 2 : ℕ) by push_cast; nlinarith)
      (show -2 * sigma ≤ (-2 : ℝ) by linarith)
    apply h.trans_eq
    rw [Real.rpow_neg (by positivity)]
    norm_num [Real.rpow_ofNat, Nat.cast_pow, ← pow_mul]
  rw [stripError_sq]
  have h0 := mul_le_mul_of_nonneg_left he
    (by positivity : 0 ≤ 4 * (q : ℝ) ^ 2 * (1 + y) ^ 2)
  apply h0.trans
  have hny : (q : ℝ) * y ≤ N := hp.2.2.1
  have hc : ((q : ℝ) * y) ^ 3 ≤ (N : ℝ) ^ 4 := by
    have h3 := pow_le_pow_left₀ (by positivity) hny 3
    have h4 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 :=
      pow_le_pow_right₀ (by linarith) (by norm_num : 3 ≤ 4)
    exact h3.trans h4
  have hab : (1 + y) ^ 2 ≤ 4 * y ^ 2 := by nlinarith
  apply (le_div_iff₀ (mul_pos hq0 hy0)).mpr
  apply (mul_le_mul_iff_left₀ (pow_pos hn0 4)).mp
  have hc' := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 16)
  have hab' := mul_le_mul_of_nonneg_left hab
    (by positivity : 0 ≤ 4 * (q : ℝ) ^ 3 * y)
  field_simp
  nlinarith only [hc', hab']

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
