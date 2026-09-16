import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.DerivativeBounds
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaValidation

def sineJet : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => -sineJet n

def sincApprox (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (sineJet (k + 1) : ℚ) * x ^ k / (k + 1).factorial

def sincPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (sineJet (k + 1) : ℝ) * x ^ k / (k + 1).factorial

theorem sincApprox_cast (n : ℕ) (x : ℚ) :
    (sincApprox n x : ℝ) = sincPolynomial n x := by
  simp [sincApprox, sincPolynomial]

theorem sineJet_correct (n : ℕ) : iteratedDeriv n Real.sin 0 = (sineJet n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [sineJet]
  | one => simp [sineJet]
  | more n hn _ =>
    rw [show n + 2 = (n + 1) + 1 by omega, Real.iteratedDeriv_add_one_sin,
      Real.iteratedDeriv_add_one_cos]
    simpa only [Pi.neg_apply, sineJet, Int.cast_neg] using congrArg Neg.neg hn

theorem sincPolynomial_zero (n : ℕ) : sincPolynomial n 0 = 1 := by
  simp [sincPolynomial, zero_pow_eq, ite_div, sineJet]

theorem sine_taylor_eq (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    taylorWithinEval Real.sin (n + 1) (uIcc 0 x) 0 x = x * sincPolynomial n x := by
  have hu : UniqueDiffOn ℝ (uIcc 0 x) := uniqueDiffOn_Icc (by
    rcases lt_or_gt_of_ne hx with h | h
    · simpa only [min_eq_right h.le, max_eq_left h.le] using h
    · simpa only [min_eq_left h.le, max_eq_right h.le] using h)
  rw [taylor_within_apply]
  simp_rw [iteratedDerivWithin_eq_iteratedDeriv hu Real.contDiff_sin.contDiffAt (left_mem_uIcc),
    sineJet_correct]
  rw [Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one,
    sineJet, Int.cast_zero, add_zero, sub_zero, smul_eq_mul, mul_zero]
  unfold sincPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ]
  ring

theorem sincPolynomial_error (n : ℕ) (x : ℝ) :
    |Real.sinc x - sincPolynomial n x| ≤ |x| ^ (n + 1) / (n + 2).factorial := by
  by_cases hx : x = 0
  · simp [hx, sincPolynomial_zero]
  obtain ⟨y, _, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.sin) (n := n + 1) (x₀ := 0) (x := x) (Ne.symm hx) Real.contDiff_sin.contDiffOn
  rw [sine_taylor_eq n hx, sub_zero] at he
  have hb : |Real.sin x - x * sincPolynomial n x| ≤
      |x| ^ (n + 2) / (n + 2).factorial := by
    rw [he, abs_div, abs_mul, abs_pow, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (Real.abs_iteratedDeriv_sin_le_one (n + 1 + 1) y) (pow_nonneg (abs_nonneg x) _)
  apply (mul_le_mul_iff_right₀ (abs_pos.mpr hx)).mp
  calc
    |x| * |Real.sinc x - sincPolynomial n x| =
        |Real.sin x - x * sincPolynomial n x| := by
      rw [← abs_mul, mul_sub, rs_sinc_mul]
    _ ≤ |x| ^ (n + 2) / (n + 2).factorial := hb
    _ = _ := by
      rw [show |x| ^ (n + 2) = |x| * |x| ^ (n + 1) from pow_succ' _ _, mul_div_assoc]

theorem sinc_integral (x : ℝ) :
    Real.sinc x = ∫ t : ℝ in 0..1, Real.cos (t * x) := by
  by_cases hx : x = 0
  · simp [hx]
  have he := intervalIntegral.mul_integral_comp_mul_right (f := Real.cos) (a := 0) (b := 1) x
  rw [zero_mul, one_mul, integral_cos, Real.sin_zero, sub_zero] at he
  rw [Real.sinc_of_ne_zero hx]
  exact (div_eq_iff hx).mpr (by linarith)

theorem sinc_lipschitz (x y : ℝ) : |Real.sinc x - Real.sinc y| ≤ |x - y| := by
  rw [sinc_integral x, sinc_integral y, ← intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := |x - y|)
    (f := fun t : ℝ => Real.cos (t * x) - Real.cos (t * y)) (by
      intro t ht
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      rw [Real.norm_eq_abs]
      apply (Real.abs_cos_sub_cos_le _ _).trans
      rw [← mul_sub, abs_mul, abs_of_nonneg ht'.1.le]
      nlinarith [abs_nonneg (x - y), ht'.2])
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

def sincError (n : ℕ) (x e : ℚ) : ℚ := |x| ^ (n + 1) / (n + 2).factorial + e

theorem sincApprox_error (n : ℕ) (x e : ℚ) {y : ℝ} (he : |y - x| ≤ (e : ℝ)) :
    |Real.sinc y - (sincApprox n x : ℝ)| ≤ (sincError n x e : ℝ) := by
  have h := abs_sub_le (Real.sinc y) (Real.sinc (x : ℝ)) (sincPolynomial n x)
  rw [sincApprox_cast]
  have h1 := (sinc_lipschitz y x).trans he
  have h2 := sincPolynomial_error n (x : ℝ)
  simp only [sincError, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast]
  linarith

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
