import Mathlib.Data.Nat.Factorization.Root
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import AnalyticNumberTheory.Sieve.SelbergUpperBound
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

def positiveBelow (y : ℝ) : Finset ℕ := Ico 1 ⌈y⌉₊

theorem mem_positiveBelow {n : ℕ} {y : ℝ} :
    n ∈ positiveBelow y ↔ 0 < n ∧ (n : ℝ) < y := by
  rw [positiveBelow, mem_Ico]
  exact and_congr (by omega) Nat.lt_ceil

theorem positiveBelow_card {y : ℝ} (hy : 0 < y) :
    ((positiveBelow y).card : ℝ) = (⌈y⌉₊ : ℝ) - 1 := by
  have h : 1 ≤ ⌈y⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hy).ne'
  simp [positiveBelow, Nat.cast_sub h]

theorem positiveBelow_card_bounds {y : ℝ} (hy : 0 < y) :
    y - 1 ≤ ((positiveBelow y).card : ℝ) ∧ ((positiveBelow y).card : ℝ) ≤ y := by
  rw [positiveBelow_card hy]
  constructor
  · linarith [Nat.le_ceil y]
  · linarith [Nat.ceil_lt_add_one hy.le]

theorem floorRoot_two_eq_one_iff {n : ℕ} :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro h
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpn
    have hd : p ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by
      simpa [pow_two] using hpn)
    rw [h] at hd
    exact hp.ne_one (Nat.dvd_one.mp hd)
  · intro hs
    have hsq := Nat.floorRoot_pow_dvd (n := 2) (a := n)
    by_contra h
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
    have hd := (pow_dvd_pow_of_dvd hpd 2).trans hsq
    exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp) (by simpa [pow_two] using hd)

theorem square_divisor_identity (n : ℕ) :
    |(μ n : ℝ)| = ∑ d ∈ (Nat.floorRoot 2 n).divisors, (μ d : ℝ) := by
  rw [AnalyticNumberTheory.Sieve.sum_moebius_eq_one,
    ← Int.cast_abs, ArithmeticFunction.abs_moebius]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, floorRoot_two_eq_one_iff]

theorem square_divisor_identity_below {y : ℝ} {n : ℕ}
    (hn : n ∈ positiveBelow y) :
    |(μ n : ℝ)| =
      ∑ d ∈ positiveBelow (Real.sqrt y), if d ^ 2 ∣ n then (μ d : ℝ) else 0 := by
  classical
  obtain ⟨hn0, hny⟩ := mem_positiveBelow.mp hn
  have he : (Nat.floorRoot 2 n).divisors =
      (positiveBelow (Real.sqrt y)).filter (fun d => d ^ 2 ∣ n) := by
    ext d
    rw [Nat.mem_divisors, Nat.floorRoot_ne_zero, mem_filter, mem_positiveBelow,
      ← Nat.pow_dvd_iff_dvd_floorRoot]
    constructor
    · rintro ⟨hd, _⟩
      have hd0 : 0 < d := Nat.pos_of_ne_zero (by
        intro h; subst d; exact hn0.ne' (by simpa using hd))
      have hdn : (d : ℝ) ^ 2 ≤ n := by
        exact_mod_cast Nat.le_of_dvd hn0 hd
      exact ⟨⟨hd0, (Real.lt_sqrt (Nat.cast_nonneg d)).mpr (hdn.trans_lt hny)⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by decide, hn0.ne'⟩
  rw [square_divisor_identity n, he, sum_filter]

theorem strict_multiples_card {y : ℝ} {d : ℕ} (hd : 0 < d) :
    ((positiveBelow y).filter (fun n => d ∣ n)).card =
      (positiveBelow (y / d)).card := by
  classical
  symm
  apply card_bij (fun k _ => d * k)
  · intro k hk
    obtain ⟨hk0, hk⟩ := mem_positiveBelow.mp hk
    rw [mem_filter, mem_positiveBelow]
    exact ⟨⟨Nat.mul_pos hd hk0, by
      rw [Nat.cast_mul]
      simpa [mul_comm] using (lt_div_iff₀ (Nat.cast_pos.mpr hd)).mp hk⟩,
      dvd_mul_right _ _⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro n hn
    obtain ⟨hn, k, rfl⟩ := mem_filter.mp hn
    obtain ⟨hn0, hn⟩ := mem_positiveBelow.mp hn
    refine ⟨k, mem_positiveBelow.mpr ⟨by nlinarith, ?_⟩, rfl⟩
    rw [lt_div_iff₀ (Nat.cast_pos.mpr hd)]
    simpa [Nat.cast_mul, mul_comm] using hn

def squarefreeCount (y : ℝ) : ℝ :=
  ∑ n ∈ positiveBelow y, |(μ n : ℝ)|

theorem squarefreeCount_eq_strict_multiples (y : ℝ) :
    squarefreeCount y = ∑ d ∈ positiveBelow (Real.sqrt y),
      (μ d : ℝ) * ((positiveBelow (y / (d : ℝ) ^ 2)).card : ℝ) := by
  classical
  unfold squarefreeCount
  rw [sum_congr rfl (fun n hn => square_divisor_identity_below hn)]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter, sum_const, nsmul_eq_mul, strict_multiples_card
    (pow_pos (mem_positiveBelow.mp hd).1 2), Nat.cast_pow, mul_comm]

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic
