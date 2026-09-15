import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.RightParameters

/-! # Actual all-nonprincipal right-line mean, including sigma = 1 -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

theorem right_finite_cost (q : ℕ) [NeZero q] {y : ℝ} (hy : 2 ≤ y) :
    (4 * y / ⌈(q : ℝ) * y⌉₊ +
      12 / (q : ℝ) * harmonicRange ((⌈(q : ℝ) * y⌉₊ ^ 2 * ⌈(q : ℝ) * y⌉₊ + 1) / q + 1)) *
        liuHarmonic (⌈(q : ℝ) * y⌉₊ ^ 2 * ⌈(q : ℝ) * y⌉₊) ^ 4 ≤
      16384 * (1 + Real.log ((q : ℝ) * y)) ^ 5 / q := by
  let N := ⌈(q : ℝ) * y⌉₊
  let L := 1 + Real.log ((q : ℝ) * y)
  have hp := ceil_parameters q hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hz : 2 ≤ (q : ℝ) * y := by nlinarith
  have hh := right_harmonics q N hz hp.1 hp.2.2.2
  have hL : 1 ≤ L := (right_log_N hz hp.1 hp.2.2.2).1
  have hq0 : (0 : ℝ) < q := by positivity
  have hn0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by dsimp [N]; omega)
  have hyN : 4 * y / (N : ℝ) ≤ 4 / (q : ℝ) := by
    apply (div_le_div_iff₀ hn0 hq0).mpr
    nlinarith only [hp.2.2.1]
  have hfac : 4 * y / (N : ℝ) +
      12 / (q : ℝ) * harmonicRange ((N ^ 2 * N + 1) / q + 1) ≤ 64 * L / q := by
    have hb := mul_le_mul_of_nonneg_left hh.2.1
      (by positivity : 0 ≤ 12 / (q : ℝ))
    have hLq := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ (q : ℝ)⁻¹)
    dsimp [L] at hLq
    simp only [div_eq_mul_inv] at hyN hb ⊢
    dsimp [L]
    linarith
  have hh0 : 0 ≤ liuHarmonic (N ^ 2 * N) := by unfold liuHarmonic; positivity
  have hpow := pow_le_pow_left₀ hh0 hh.1 4
  have hm := mul_le_mul hfac hpow (by positivity)
    (by positivity : 0 ≤ 64 * L / q)
  exact hm.trans_eq (by dsimp [L]; ring)

theorem Fmean_right_explicit (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : 1 ≤ sigma) :
    Fmean q ((q : ℝ) * y) sigma y ≤
      18048 * (1 + Real.log ((q : ℝ) * y)) ^ 5 / q := by
  let N := ⌈(q : ℝ) * y⌉₊
  let L := 1 + Real.log ((q : ℝ) * y)
  have hp := ceil_parameters q hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hz : 2 ≤ (q : ℝ) * y := by nlinarith
  have hL : 1 ≤ L := (right_log_N hz hp.1 hp.2.2.2).1
  have hq0 : (0 : ℝ) < q := by positivity
  have hy0 : 0 < y := by linarith
  have hNN : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) N
  have h := Fmean_right_mother q ((q : ℝ) * y) (by linarith) hNN hp.2.1 hs hy0.le
  have he := right_error_cost q hy hs
  have hQ := right_mollifier_cost q hy
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)) hQ
    (mollifierMeanBound_nonneg q _ hy0.le)
    (by positivity : 0 ≤ 2 * (16 / ((q : ℝ) * y)))
  have hre : 2 * stripError q (N ^ 2) sigma y ^ 2 *
      mollifierMeanBound q ((q : ℝ) * y) y ≤ 1664 * L ^ 2 / q := by
    apply hm.trans_eq
    dsimp [L]
    field_simp
    ring
  have hpow : L ^ 2 ≤ L ^ 5 := pow_le_pow_right₀ hL (by norm_num : 2 ≤ 5)
  have hlast := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 1664 / (q : ℝ))
  have hr := h.trans (add_le_add (right_finite_cost q hy) hre)
  dsimp [L] at hlast
  simp only [div_eq_mul_inv] at hr hlast ⊢
  nlinarith only [hr, hlast]

theorem nonprincipal_right_integral_sum (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : 1 ≤ sigma) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖f chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
      (q.totient : ℝ) * (18048 * (1 + Real.log ((q : ℝ) * y)) ^ 5 / q) := by
  have h := Fmean_right_explicit q hy hs
  unfold Fmean at h
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  exact ((div_le_iff₀ hphi).mp h).trans_eq (mul_comm _ _)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
