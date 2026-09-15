import LiuWang.Proof.GlobalZeroDensity.Strip.MovingRight
import Mathlib.Analysis.Complex.Hadamard

/-! Actual boundedness, including the removable point, on the closed moving strip. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity.Sharp
open Complex.HadamardThreeLines

namespace LiuWang.Proof.GlobalZeroDensity.Strip

theorem closed_strip_safe {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs : s ∈ verticalClosedStrip (1 / 2) (1 + delta y)) :
    s ∈ regularStrip y := by
  have hd := delta_bounds hy
  change 1 / 2 ≤ s.re ∧ s.re ≤ 1 + delta y at hs
  change 0 < s.re ∧ s.re < Real.pi * y
  constructor
  · linarith
  · nlinarith [Real.pi_gt_three]

theorem norm_Q_strip_le {s : ℂ} (hs : 0 ≤ s.re) (y : ℝ) :
    ‖Q y s‖ ≤ (⌈y⌉₊ : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range ⌈y⌉₊, ‖(ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range ⌈y⌉₊, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n = 0
      · subst n; simp
      have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
      rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hpow := Real.one_le_rpow hn1 hs
      apply (div_le_one (by positivity)).mpr
      exact hmu.trans hpow
    _ = _ := by simp

theorem norm_regularG_decay {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : 1 / 2 ≤ s.re) (hs4 : s.re ≤ 4) :
    ‖regularG y s‖ ≤ (200 / 99) * ‖f y s‖ * Real.exp (- |s.im| / (2 * y)) := by
  have hc := norm_cos_ge_exp_sharp (s / (2 * (y : ℂ)))
    (cosine_re_small hy (by linarith) hs4)
  have hi : |(s / (2 * (y : ℂ))).im| = |s.im| / (2 * y) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
    simp [abs_div, abs_of_nonneg (show 0 ≤ y by linarith), abs_mul]
  rw [hi] at hc
  have hsp : 0 < ‖s‖ := by have := Complex.re_le_norm s; linarith
  have hcp : 0 < ‖Complex.cos (s / (2 * (y : ℂ)))‖ :=
    (by positivity : 0 < (99 / 200) * Real.exp (|s.im| / (2 * y))).trans_le hc
  have hinv : 1 / ‖Complex.cos (s / (2 * (y : ℂ)))‖ ≤
      (200 / 99) * Real.exp (- |s.im| / (2 * y)) := by
    have h := one_div_le_one_div_of_le (by positivity) hc
    have he : 1 / ((99 / 200) * Real.exp (|s.im| / (2 * y))) =
        (200 / 99) * Real.exp (- |s.im| / (2 * y)) := by
      rw [neg_div, Real.exp_neg]
      field_simp
    exact h.trans_eq he
  have hr : ‖s - 1‖ / (‖s‖ * ‖Complex.cos (s / (2 * (y : ℂ)))‖) ≤
      (200 / 99) * Real.exp (- |s.im| / (2 * y)) := by
    calc
      _ ≤ ‖s‖ / (‖s‖ * ‖Complex.cos (s / (2 * (y : ℂ)))‖) :=
        div_le_div_of_nonneg_right (norm_sub_one_le hs0) (mul_pos hsp hcp).le
      _ = 1 / ‖Complex.cos (s / (2 * (y : ℂ)))‖ := by field_simp
      _ ≤ _ := hinv
  rw [regularG_eq_g hs1, g, norm_mul, norm_div, norm_mul]
  have h := mul_le_mul_of_nonneg_right hr (norm_nonneg (f y s))
  nlinarith

theorem regularG_high_bound {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs : s ∈ verticalClosedStrip (1 / 2) (1 + delta y)) (ht : 1 ≤ |s.im|) :
    ‖regularG y s‖ ≤ (200 / 99) * ((8 + 4 * y) * (⌈y⌉₊ : ℝ) + 1) := by
  have hd := delta_bounds hy
  change 1 / 2 ≤ s.re ∧ s.re ≤ 1 + delta y at hs
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at ht
  have hz := norm_riemannZeta_lt_linear_im_on_strip s ⟨hs.1, by linarith⟩ ht
  have hq := norm_Q_strip_le (by linarith : 0 ≤ s.re) y
  have hmul := mul_le_mul hz.le hq (norm_nonneg _) (by positivity)
  have hf := norm_sub_le (riemannZeta s * Q y s) 1
  rw [norm_mul, norm_one] at hf
  have hdec := norm_regularG_decay hy hs1 hs.1 (by linarith)
  have hy0 : 0 < y := by linarith
  have he : Real.exp (- |s.im| / (2 * y)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith [abs_nonneg s.im]) (by positivity))
  have hp := (Real.mul_exp_neg_le_exp_neg_one (|s.im| / (2 * y))).trans
    (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * y by positivity)
  have heq : 2 * y * (|s.im| / (2 * y) * Real.exp (-(|s.im| / (2 * y)))) =
      |s.im| * Real.exp (- |s.im| / (2 * y)) := by rw [neg_div]; field_simp
  rw [heq] at hp'
  have hf' : ‖f y s‖ ≤ (8 + 2 * |s.im|) * (⌈y⌉₊ : ℝ) + 1 := by
    change ‖riemannZeta s * Q y s - 1‖ ≤ _
    linarith
  have hweighted := mul_le_mul_of_nonneg_right hf' (Real.exp_pos (- |s.im| / (2 * y))).le
  have hN1 := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 8 * (⌈y⌉₊ : ℝ) + 1 by positivity)
  have hN2 := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 2 * (⌈y⌉₊ : ℝ) by positivity)
  nlinarith

theorem regularG_bounded {y : ℝ} (hy : 10000 ≤ y) :
    BddAbove ((norm ∘ regularG y) '' verticalClosedStrip (1 / 2) (1 + delta y)) := by
  let K : Set ℂ := {s | s.re ∈ Icc (1 / 2) (1 + delta y) ∧ s.im ∈ Icc (-1) 1}
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (regularG y) K := by
    intro s hs
    exact (differentiableAt_regularG (by linarith : 0 < y)
      (closed_strip_safe hy hs.1)).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hc.norm
  refine ⟨max B ((200 / 99) * ((8 + 4 * y) * (⌈y⌉₊ : ℝ) + 1)), ?_⟩
  rintro v ⟨s, hs, rfl⟩
  by_cases ht : 1 ≤ |s.im|
  · exact (regularG_high_bound hy hs ht).trans (le_max_right _ _)
  · have hsK : s ∈ K := ⟨hs, abs_le.mp (le_of_lt (lt_of_not_ge ht))⟩
    exact (hB (mem_image_of_mem _ hsK)).trans (le_max_left _ _)

end LiuWang.Proof.GlobalZeroDensity.Strip
