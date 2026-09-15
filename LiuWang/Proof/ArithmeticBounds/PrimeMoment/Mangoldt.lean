import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! 显式初等 Mertens 界。保留完整 Λ 支撑，不使用渐近存在常数。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.PrimeMoment

open scoped BigOperators
open Finset Real
open scoped ArithmeticFunction.vonMangoldt

def mangoldtReciprocal (x : ℝ) : ℝ :=
  ∑ d ∈ Icc 0 ⌊x⌋₊, Λ d / d

theorem log_sum_eq_mangoldt_floor (n : ℕ) :
    (∑ k ∈ Ioc 0 n, log k) = ∑ d ∈ Ioc 0 n, Λ d * (n / d : ℕ) := by
  simpa using ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.vonMangoldt) n

theorem log_sum_lower (n : ℕ) :
    (n : ℝ) * log n - n ≤ ∑ k ∈ Ioc 0 n, log k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le n)]
    rcases n.eq_zero_or_pos with rfl | hn
    · norm_num
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := log_le_sub_one_of_pos
      (show 0 < ((n : ℝ) + 1) / n by positivity)
    rw [log_div (by positivity) hn0.ne'] at hlog
    have hmul := (mul_le_mul_of_nonneg_left hlog hn0.le)
    have hid : (n : ℝ) * (((n : ℝ) + 1) / n - 1) = 1 := by
      field_simp
      ring
    rw [hid] at hmul
    push_cast
    nlinarith

theorem log_sum_upper (n : ℕ) :
    (∑ k ∈ Ioc 0 n, log k) ≤ (n : ℝ) * log n := by
  calc
    _ ≤ ∑ _k ∈ Ioc 0 n, log n := by
      apply sum_le_sum
      intro k hk
      have hk' := mem_Ioc.mp hk
      exact log_le_log (by exact_mod_cast hk'.1) (by exact_mod_cast hk'.2)
    _ = _ := by simp

theorem mangoldtReciprocal_nat (n : ℕ) :
    mangoldtReciprocal n = ∑ d ∈ Ioc 0 n, Λ d / d := by
  simp [mangoldtReciprocal, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]

theorem mangoldtReciprocal_nat_bounds {n : ℕ} (hn : 1 ≤ n) :
    log n - 1 ≤ mangoldtReciprocal n ∧
      mangoldtReciprocal n ≤ log n + 6 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : (∑ k ∈ Ioc 0 n, log k) ≤ (n : ℝ) * mangoldtReciprocal n := by
    rw [log_sum_eq_mangoldt_floor, mangoldtReciprocal_nat, mul_sum]
    apply sum_le_sum
    intro d hd
    calc
      _ ≤ Λ d * ((n : ℝ) / d) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by ring
  have hhi : (n : ℝ) * mangoldtReciprocal n ≤
      (∑ k ∈ Ioc 0 n, log k) + Chebyshev.psi n := by
    rw [log_sum_eq_mangoldt_floor, Chebyshev.psi, Nat.floor_natCast,
      mangoldtReciprocal_nat, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    have hf : (n : ℝ) / d ≤ (n / d : ℕ) + 1 := by
      simpa [Nat.floor_div_natCast] using (Nat.lt_floor_add_one ((n : ℝ) / d)).le
    have := mul_le_mul_of_nonneg_left hf (ArithmeticFunction.vonMangoldt_nonneg (n := d))
    convert this using 1 <;> ring
  have hpsi : Chebyshev.psi n ≤ 6 * (n : ℝ) := by
    apply (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)).trans
    have : log 4 ≤ (2 : ℝ) := by rw [log_four_eq]; linarith [log_two_lt_d9]
    nlinarith
  constructor
  · have := log_sum_lower n
    nlinarith
  · have := log_sum_upper n
    nlinarith

theorem mangoldtReciprocal_bounds {x : ℝ} (hx : 1 ≤ x) :
    log x - 2 ≤ mangoldtReciprocal x ∧
      mangoldtReciprocal x ≤ log x + 6 := by
  have hx0 : 0 < x := by linarith
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hn0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hfloor := Nat.floor_le hx0.le
  have hnear : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hlog : log x ≤ log (⌊x⌋₊ : ℝ) + 1 := by
    have h := log_le_log hx0 hnear
    rw [log_mul (by norm_num) hn0.ne'] at h
    linarith [log_two_lt_d9]
  have heq : mangoldtReciprocal (⌊x⌋₊ : ℝ) = mangoldtReciprocal x := by
    simp [mangoldtReciprocal]
  have h := mangoldtReciprocal_nat_bounds hn
  rw [heq] at h
  constructor
  · linarith [h.1]
  · linarith [h.2, log_le_log hn0 hfloor]

end LiuWang.Proof.ArithmeticBounds.PrimeMoment
