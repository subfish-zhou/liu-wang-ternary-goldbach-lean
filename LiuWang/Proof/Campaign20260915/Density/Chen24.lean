import LiuWang.Proof.GlobalZeroDensity.Sharp.DetectorMean
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.QBoundary
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! The actual strict-cutoff mollifier mean, with squarefree weights retained
in the off-diagonal kernel. No mean-value estimate is assumed. -/

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory
open scoped ArithmeticFunction.Moebius
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

namespace LiuWang.Proof.Campaign20260915.Density

theorem strict_cutoff_eq_positiveBelow (y : ℝ) :
    (range ⌈y⌉₊).erase 0 = positiveBelow y := by
  ext n
  simp only [mem_erase, mem_range, positiveBelow, mem_Ico]
  omega

theorem harmonic_cutoff_budget {y : ℝ} (hy : 10000 ≤ y) :
    (∑ n ∈ range ⌈y⌉₊, (n : ℝ)⁻¹) ≤ Real.log y + 0.7 := by
  have hN : 6 ≤ ⌈y⌉₊ := by
    have h := Nat.le_ceil y
    by_contra hnot
    have hn : (⌈y⌉₊ : ℝ) ≤ 5 := by
      exact_mod_cast (show ⌈y⌉₊ ≤ 5 by omega)
    linarith
  have h := (Real.strictAnti_eulerMascheroniSeq'.antitone hN).trans_lt
    Real.eulerMascheroniSeq'_six_lt_two_thirds
  simp only [Real.eulerMascheroniSeq', show ⌈y⌉₊ ≠ 0 by omega, if_false] at h
  have he : (∑ n ∈ range (⌈y⌉₊ + 1), (n : ℝ)⁻¹) = (harmonic ⌈y⌉₊ : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sub _ (by omega : 1 ≤ ⌈y⌉₊ + 1)]
    simp
  rw [← he, sum_range_succ] at h
  have hinv : (0 : ℝ) ≤ (⌈y⌉₊ : ℝ)⁻¹ := by positivity
  linarith [(ceil_log_bounds hy).2]

theorem squarefree_count_budget {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    squarefreeCount y ≤ (5 / 8) * y := by
  have hyb := source_height_lower hy
  have hy0 : 0 ≤ y := by linarith
  have hs : 133 ≤ Real.sqrt y := by
    nlinarith [Real.sq_sqrt hy0, Real.sqrt_nonneg y]
  have hsmall : 2 * Real.sqrt y + 1 ≤ 0.017 * y := by
    nlinarith [Real.sq_sqrt hy0, sq_nonneg (Real.sqrt y - 133)]
  have h := squarefreeCount_upper (show 1 ≤ y by linarith)
  have hc := mul_le_mul_of_nonneg_right euler_density_bounds.2 hy0
  linarith

theorem weighted_coefficient_gap {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hne : m ≠ n) :
    ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n| ≤
      |(μ m : ℝ)| / |(m : ℝ) - n| +
        (1 / 2) * ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ := by
  have hk := logarithmic_kernel_abs_le (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn)
    (show (m : ℝ) ≠ n by exact_mod_cast hne)
  have hw := mul_le_mul_of_nonneg_left hk
    (mul_nonneg (abs_nonneg (μ m : ℝ)) (abs_nonneg (μ n : ℝ)))
  have hn1 : |(μ n : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hg := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hn1 (abs_nonneg (μ m : ℝ)))
    (abs_nonneg ((m : ℝ) - n))
  calc
    _ = |(μ m : ℝ)| * |(μ n : ℝ)| *
        (1 / (Real.sqrt m * Real.sqrt n * |Real.log m - Real.log n|)) := by
      rw [norm_criticalCoefficient hm, norm_criticalCoefficient hn]
      ring
    _ ≤ _ := hw
    _ = |(μ m : ℝ)| * |(μ n : ℝ)| / |(m : ℝ) - n| +
        (1 / 2) * ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ := by
      rw [norm_criticalCoefficient hm, norm_criticalCoefficient hn]
      ring
    _ ≤ _ := add_le_add (by simpa only [mul_one] using hg) le_rfl

theorem off_diagonal_squarefree (y : ℝ) :
    (∑ m ∈ (range ⌈y⌉₊).erase 0, ∑ n ∈ ((range ⌈y⌉₊).erase 0).erase m,
      ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n|) ≤
      2 * squarefreeCount y * (∑ k ∈ range ⌈y⌉₊, (k : ℝ)⁻¹) +
        (1 / 2) * (∑ n ∈ positiveBelow y, |(μ n : ℝ)| / Real.sqrt n) ^ 2 := by
  let S := (range ⌈y⌉₊).erase 0
  have hrow (m : ℕ) (hm : m ∈ S) :
      (∑ n ∈ S.erase m, |(μ m : ℝ)| / |(m : ℝ) - n|) ≤
        2 * |(μ m : ℝ)| * (∑ k ∈ range ⌈y⌉₊, (k : ℝ)⁻¹) := by
    calc
      _ ≤ ∑ n ∈ range ⌈y⌉₊, |(μ m : ℝ)| / |(m : ℝ) - n| :=
        sum_le_sum_of_subset_of_nonneg
          ((erase_subset _ _).trans (erase_subset _ _)) (fun _ _ _ => by positivity)
      _ = |(μ m : ℝ)| * ∑ n ∈ range ⌈y⌉₊, 1 / |(m : ℝ) - n| := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (reciprocal_gap_row (mem_range.mp (mem_erase.mp hm).2))
        (abs_nonneg (μ m : ℝ))).trans_eq (by ring)
  have hsum := sum_le_sum hrow
  have hcount : (∑ m ∈ S, |(μ m : ℝ)|) = squarefreeCount y := by
    rw [show S = positiveBelow y from strict_cutoff_eq_positiveBelow y]
    rfl
  simp only [← sum_mul, ← mul_sum, hcount] at hsum
  have hsmooth :
      (∑ m ∈ S, ∑ n ∈ S.erase m,
        (1 / 2) * ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖) ≤
        (1 / 2) * (∑ n ∈ S, ‖criticalCoefficient n‖) ^ 2 := by
    calc
      _ ≤ ∑ m ∈ S, ∑ n ∈ S,
          (1 / 2) * ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ := by
        apply sum_le_sum
        intro m _
        exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
      _ = _ := by
        simp only [← mul_sum, ← sum_mul]
        ring
  have he : (∑ n ∈ S, ‖criticalCoefficient n‖) =
      ∑ n ∈ positiveBelow y, |(μ n : ℝ)| / Real.sqrt n := by
    rw [show S = positiveBelow y from strict_cutoff_eq_positiveBelow y]
    exact sum_congr rfl (fun n hn => norm_criticalCoefficient (mem_positiveBelow.mp hn).1)
  rw [he] at hsmooth
  have hpoint :
      (∑ m ∈ S, ∑ n ∈ S.erase m,
        ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n|) ≤
      ∑ m ∈ S, ∑ n ∈ S.erase m,
        (|(μ m : ℝ)| / |(m : ℝ) - n| +
          (1 / 2) * ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖) := by
    apply sum_le_sum
    intro m hm
    apply sum_le_sum
    intro n hn
    exact weighted_coefficient_gap (Nat.pos_of_ne_zero (mem_erase.mp hm).1)
      (Nat.pos_of_ne_zero (mem_erase.mp (mem_erase.mp hn).2).1)
      (mem_erase.mp hn).1.symm
  simp only [sum_add_distrib] at hpoint
  exact hpoint.trans (add_le_add hsum hsmooth)

theorem chen24_mollifier_mean {y u : ℝ}
    (hy : 10000 * Real.log 6 ≤ y) (hu : 0 ≤ u) :
    (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      y * (2.19021 * u + 2.906) * Real.log y := by
  have hyb := source_height_lower hy
  have hy0 : 0 ≤ y := by linarith
  have hy' : 10000 ≤ y := by linarith
  have hL := (source_height_log_bounds hy).2
  have hh := harmonic_cutoff_budget hy'
  have hc := squarefree_count_budget hy
  have hS := (equation_11 (show 1 ≤ y by linarith)).trans (sqrt_boundary_scalar hy)
  have hS0 : 0 ≤ ∑ n ∈ positiveBelow y, |(μ n : ℝ)| / Real.sqrt n := by positivity
  have hS2 := pow_le_pow_left₀ hS0 hS 2
  rw [mul_pow, Real.sq_sqrt hy0] at hS2
  have hC0 : 0 ≤ squarefreeCount y := by unfold squarefreeCount; positivity
  have hprod := mul_le_mul hc hh (by positivity)
    (show 0 ≤ (5 / 8 : ℝ) * y by positivity)
  have hoff := off_diagonal_squarefree y
  have hdiag := mul_le_mul_of_nonneg_left
    ((mollifier_energy_le_inverse_range ⌈y⌉₊).trans hh)
    (show 0 ≤ 2 * (y * u) by positivity)
  have hmean := Q_mean_diagonal_offDiagonal y (show 0 ≤ y * u by positivity)
  have huL : 2 * u * (Real.log y + 0.7) ≤ 2.19021 * u * Real.log y := by
    have h := mul_le_mul_of_nonneg_right
      (show 2 * (Real.log y + 0.7) ≤ 2.19021 * Real.log y by linarith) hu
    nlinarith only [h]
  have hcL : (5 / 2 : ℝ) * (Real.log y + 0.7) + 1.3071 ^ (2 : ℕ) ≤
      2.906 * Real.log y := by linarith
  have huLy := mul_le_mul_of_nonneg_left huL hy0
  have hcLy := mul_le_mul_of_nonneg_left hcL hy0
  nlinarith only [hprod, hoff, hdiag, hmean, hS2, huLy, hcLy]

#print axioms chen24_mollifier_mean

end LiuWang.Proof.Campaign20260915.Density
