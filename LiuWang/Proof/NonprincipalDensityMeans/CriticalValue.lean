import LiuWang.Proof.NonprincipalDensityMeans.LFunction

/-!
# An explicit critical value bound from the actual character prefix

This deliberately elementary bound is uniform for imprimitive characters.
Its constant is derived from a finite cutoff, not borrowed from Chen.
-/

set_option autoImplicit false
noncomputable section

open Finset
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans

theorem partialL_critical_norm_le {q : ℕ} (chi : Character q) (M : ℕ) (t : ℝ) :
    ‖partialL chi M ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ 2 * Real.sqrt M := by
  have hnorm : ∀ n ∈ (range M).erase 0,
      ‖(1 : ℂ) * chi n / (n : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
        (Real.sqrt n)⁻¹ := by
    intro n hn
    have hn0 := Nat.pos_of_ne_zero (mem_erase.mp hn).1
    rw [one_mul, norm_div, Complex.norm_natCast_cpow_of_pos hn0]
    have hr : ((1 / 2 : ℂ) + t * Complex.I).re = (1 / 2 : ℝ) := by simp
    rw [hr, ← Real.sqrt_eq_rpow, ← one_div]
    exact div_le_div_of_nonneg_right (chi.norm_le_one n) (Real.sqrt_nonneg _)
  calc
    _ ≤ ∑ n ∈ (range M).erase 0,
        ‖(1 : ℂ) * chi n / (n : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ (range M).erase 0, (Real.sqrt n)⁻¹ := sum_le_sum hnorm
    _ ≤ ∑ n ∈ range M, (Real.sqrt n)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := GlobalZeroDensity.sum_inv_sqrt_le M

theorem LFunction_critical_norm_sq_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {y t : ℝ} (ht : |t| ≤ y) :
    ‖chi.LFunction ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ 32 * q * (1 + y) := by
  have hy : 0 ≤ y := (abs_nonneg t).trans ht
  let A : ℝ := (q : ℝ) * (1 + y)
  let M : ℕ := ⌈A⌉₊
  have hA : 1 ≤ A := by
    have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
    dsimp [A]
    nlinarith
  have hAM : A ≤ (M : ℝ) := Nat.le_ceil A
  have hM : 1 ≤ M := by
    exact_mod_cast (hA.trans hAM)
  have hMA : (M : ℝ) ≤ 2 * A := by
    have hceil : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one (by linarith)
    dsimp [M]
    linarith
  have hroot : 0 < Real.sqrt M := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hroot2 := Real.sq_sqrt (Nat.cast_nonneg M)
  have hE : truncationError q M y ≤ 2 * Real.sqrt M := by
    unfold truncationError
    apply (div_le_iff₀ hroot).mpr
    dsimp [A] at hAM
    nlinarith
  have hL : ‖chi.LFunction ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ 4 * Real.sqrt M := by
    have hb := norm_add_le (partialL chi M ((1 / 2 : ℂ) + t * Complex.I))
      (chi.LFunction ((1 / 2 : ℂ) + t * Complex.I) -
        partialL chi M ((1 / 2 : ℂ) + t * Complex.I))
    rw [add_sub_cancel] at hb
    have hp := partialL_critical_norm_le chi M t
    have he := (LFunction_truncation_critical hchi hM ht).trans hE
    linarith
  have hs := pow_le_pow_left₀ (norm_nonneg _) hL 2
  rw [mul_pow, hroot2] at hs
  dsimp [A] at hMA
  nlinarith

end LiuWang.Proof.NonprincipalDensityMeans
