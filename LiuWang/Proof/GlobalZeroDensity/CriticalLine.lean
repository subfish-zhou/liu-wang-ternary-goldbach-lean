import LiuWang.Proof.GlobalZeroDensity.Regularization
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity

/-!
Unconditional critical-line estimates for the actual detector. These are
coarse producers, not the constants of companion Lemmas 3.2 and 3.4.
-/

set_option autoImplicit false

noncomputable section

open Finset Complex MeasureTheory

namespace LiuWang.Proof.GlobalZeroDensity

theorem inv_sqrt_le_difference {x : ℝ} (hx : 1 ≤ x) :
    (Real.sqrt x)⁻¹ ≤ 2 * (Real.sqrt x - Real.sqrt (x - 1)) := by
  have hx0 : 0 < x := by linarith
  have ha := Real.sq_sqrt hx0.le
  have hb := Real.sq_sqrt (show 0 ≤ x - 1 by linarith)
  have hab : Real.sqrt (x - 1) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
  have hpos := Real.sqrt_pos.mpr hx0
  rw [← one_div]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt (x - 1))]

theorem sum_inv_sqrt_succ_le (N : ℕ) :
    (∑ n ∈ range (N + 1), (Real.sqrt (n : ℝ))⁻¹) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hb := inv_sqrt_le_difference
      (show (1 : ℝ) ≤ (N + 1 : ℕ) by exact_mod_cast Nat.succ_pos N)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hb ⊢
    linarith

theorem sum_inv_sqrt_le (N : ℕ) :
    (∑ n ∈ range N, (Real.sqrt (n : ℝ))⁻¹) ≤ 2 * Real.sqrt N := by
  have h := sum_inv_sqrt_succ_le N
  rw [sum_range_succ] at h
  exact (le_add_of_nonneg_right (by positivity)).trans h

theorem norm_Q_critical_le (y t : ℝ) :
    ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ 2 * Real.sqrt ⌈y⌉₊ := by
  calc
    _ ≤ ∑ n ∈ range ⌈y⌉₊,
        ‖(ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^
          ((1 / 2 : ℂ) + t * Complex.I)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range ⌈y⌉₊, (Real.sqrt (n : ℝ))⁻¹ := by
      apply sum_le_sum
      intro n _
      by_cases hn : n = 0
      · subst n; simp
      have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
      rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hre : (((1 / 2 : ℂ) + t * Complex.I).re) = 1 / 2 := by simp
      rw [hre, ← Real.sqrt_eq_rpow, ← one_div]
      exact div_le_div_of_nonneg_right hmu (Real.sqrt_nonneg _)
    _ ≤ _ := sum_inv_sqrt_le _

theorem norm_zeta_critical_le (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ 4 + 2 * |t| := by
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  have hre : s.re = 1 / 2 := by simp [s]
  have hs : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [hre] at this
  have hdomain : s ∈ zetaAbelContinuationDomain :=
    mem_zetaAbelContinuationDomain_of_re hs (by
      rw [hre]; simpa only [one_div] using zetaAbelContinuationReLower_lt_half)
  have hlow : 1 / 2 ≤ ‖s - 1‖ := by
    have h := Complex.abs_re_le_norm (s - 1)
    norm_num [hre] at h
    exact h
  have hinv : 1 / ‖s - 1‖ ≤ 2 := by
    calc
      _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hlow
      _ = _ := by norm_num
  have hnorm : ‖s‖ ≤ 1 / 2 + |t| := by
    simpa [s, norm_mul] using norm_add_le (1 / 2 : ℂ) ((t : ℂ) * Complex.I)
  have h := norm_riemannZeta_le s hdomain
  rw [hre] at h
  simp only [norm_div, norm_one] at h
  change ‖riemannZeta s‖ ≤ _
  linarith

theorem F_critical_le (y t : ℝ) :
    F y ((1 / 2 : ℂ) + t * Complex.I) ≤
      ((8 + 4 * |t|) * Real.sqrt ⌈y⌉₊ + 1) ^ 2 := by
  have h := norm_sub_le
    (riemannZeta ((1 / 2 : ℂ) + t * Complex.I) *
      Q y ((1 / 2 : ℂ) + t * Complex.I)) 1
  rw [norm_mul, norm_one] at h
  have hb := mul_le_mul (norm_zeta_critical_le t) (norm_Q_critical_le y t)
    (norm_nonneg _) (by positivity)
  apply pow_le_pow_left₀ (norm_nonneg _)
  change ‖riemannZeta _ * Q y _ - 1‖ ≤ _
  nlinarith

theorem M_critical_le (y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    M y (1 / 2) u ≤ 2 * u * (((8 + 4 * u) * Real.sqrt ⌈y⌉₊ + 1) ^ 2) := by
  have hi := intervalIntegrable_F y u (σ := 1 / 2) (by norm_num)
  have hb : ∀ t ∈ Set.Icc (-u) u,
      F y (((1 / 2 : ℝ) : ℂ) + t * Complex.I) ≤
        ((8 + 4 * u) * Real.sqrt ⌈y⌉₊ + 1) ^ 2 := by
    intro t ht
    have ht' : |t| ≤ u := abs_le.mpr ht
    have h := F_critical_le y t
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    exact h.trans (pow_le_pow_left₀ (by positivity) (by
      gcongr) 2)
  have h := intervalIntegral.integral_mono_on (by linarith : -u ≤ u)
    hi intervalIntegrable_const hb
  rw [intervalIntegral.integral_const] at h
  simpa only [M, sub_neg_eq_add, ← two_mul, smul_eq_mul] using h

end LiuWang.Proof.GlobalZeroDensity
