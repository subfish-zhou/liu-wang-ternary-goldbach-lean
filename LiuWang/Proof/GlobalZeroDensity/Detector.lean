import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
The actual zeta detector in (3.35) of Liu--Wang's companion paper.
The natural ceiling implements the strict real cutoff, including integer cutoffs.
-/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory
open scoped ArithmeticFunction.zeta

namespace LiuWang.Proof.GlobalZeroDensity

def truncatedMu (y : ℝ) : ArithmeticFunction ℂ where
  toFun n := if (n : ℝ) < y then (ArithmeticFunction.moebius n : ℂ) else 0
  map_zero' := by simp

def Q (y : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ range ⌈y⌉₊, (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s

def f (y : ℝ) (s : ℂ) : ℂ := riemannZeta s * Q y s - 1

def F (y : ℝ) (s : ℂ) : ℝ := ‖f y s‖ ^ 2

def H (y : ℝ) (s : ℂ) : ℂ := 1 - f y s ^ 2

def M (y σ u : ℝ) : ℝ := ∫ t in -u..u, F y ((σ : ℂ) + t * Complex.I)

def coefficient (y : ℝ) (n : ℕ) : ℂ :=
  (truncatedMu y * (ζ : ArithmeticFunction ℂ)) n - (1 : ArithmeticFunction ℂ) n

theorem mem_cutoff {y : ℝ} {n : ℕ} :
    n ∈ range ⌈y⌉₊ ↔ (n : ℝ) < y := by
  rw [mem_range, Nat.lt_ceil]

theorem truncatedMu_apply (y : ℝ) (n : ℕ) :
    truncatedMu y n = if (n : ℝ) < y then (ArithmeticFunction.moebius n : ℂ) else 0 :=
  rfl

theorem Q_hasSum (y : ℝ) (s : ℂ) :
    LSeriesHasSum (truncatedMu y) s (Q y s) := by
  have ht (n : ℕ) : LSeries.term (truncatedMu y) s n =
      if n ∈ range ⌈y⌉₊ then (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s
      else 0 := by
    by_cases hn : n = 0
    · subst n; simp
    · simp [LSeries.term_of_ne_zero hn, truncatedMu_apply, Nat.lt_ceil, ite_div]
  change HasSum (LSeries.term (truncatedMu y) s) (Q y s)
  have hz : ∀ n ∉ range ⌈y⌉₊, LSeries.term (truncatedMu y) s n = 0 :=
    fun n hn => (ht n).trans (if_neg hn)
  have hsum := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hz
  have heq : Q y s = ∑ n ∈ range ⌈y⌉₊, LSeries.term (truncatedMu y) s n := by
    simp only [Q, ht]
    exact sum_congr rfl (fun n hn => (if_pos hn).symm)
  rw [heq]
  exact hsum

theorem coefficient_apply (y : ℝ) (n : ℕ) :
    coefficient y n =
      (∑ d ∈ n.divisors, if (d : ℝ) < y then (ArithmeticFunction.moebius d : ℂ) else 0) -
        if n = 1 then 1 else 0 := by
  simp only [coefficient, ArithmeticFunction.coe_mul_zeta_apply, truncatedMu_apply,
    ArithmeticFunction.one_apply]

theorem coefficient_eq_zero_of_lt {y : ℝ} {n : ℕ} (hn : (n : ℝ) < y) :
    coefficient y n = 0 := by
  by_cases hn0 : n = 0
  · subst n; simp [coefficient]
  have hsum := congrArg (fun a : ArithmeticFunction ℂ => a n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] at hsum
  rw [coefficient_apply, ← hsum]
  apply sub_eq_zero.mpr
  apply sum_congr rfl
  intro d hd
  exact if_pos ((Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
    (Nat.mem_divisors.mp hd).1)).trans_lt hn)

theorem coefficient_norm_le {y : ℝ} (hy : 1 < y) (n : ℕ) :
    ‖coefficient y n‖ ≤ n.divisors.card := by
  by_cases hn : n = 1
  · subst n
    rw [coefficient_eq_zero_of_lt (by simpa using hy), norm_zero]
    positivity
  rw [coefficient_apply, if_neg hn, sub_zero]
  calc
    _ ≤ ∑ d ∈ n.divisors,
        ‖if (d : ℝ) < y then (ArithmeticFunction.moebius d : ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply sum_le_sum
      intro d _
      split_ifs
      · rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
      · simp
    _ = _ := by simp

theorem f_hasSum {s : ℂ} (hs : 1 < s.re) (y : ℝ) :
    LSeriesHasSum (coefficient y) s (f y s) := by
  have hprod := ArithmeticFunction.LSeriesHasSum_mul
    (f := truncatedMu y) (g := (ζ : ArithmeticFunction ℂ)) (s := s)
    (Q_hasSum y s) (ArithmeticFunction.LSeriesHasSum_zeta hs)
  have hone : LSeriesHasSum (fun n => (1 : ArithmeticFunction ℂ) n) s 1 := by
    change HasSum (LSeries.term (fun n => (1 : ArithmeticFunction ℂ) n) s) 1
    have ht (n : ℕ) : LSeries.term (fun n => (1 : ArithmeticFunction ℂ) n) s n =
        if n = 1 then 1 else 0 := by
      by_cases hn : n = 0
      · subst n; simp
      · by_cases hn1 : n = 1 <;> simp [LSeries.term_of_ne_zero hn,
          ArithmeticFunction.one_apply, hn1]
    rw [funext ht]
    exact hasSum_ite_eq 1 1
  change LSeriesHasSum
    ((fun n => (truncatedMu y * (ζ : ArithmeticFunction ℂ)) n) -
      (fun n => (1 : ArithmeticFunction ℂ) n)) s _
  simpa only [f, mul_comm] using hprod.sub hone

theorem H_factorization (y : ℝ) (s : ℂ) :
    H y s = riemannZeta s * (Q y s * (2 - riemannZeta s * Q y s)) := by
  unfold H f
  ring

theorem H_eq_zero_of_zeta_eq_zero {s : ℂ} (hs : riemannZeta s = 0) (y : ℝ) :
    H y s = 0 := by
  rw [H_factorization, hs, zero_mul]

theorem differentiable_Q (y : ℝ) : Differentiable ℂ (Q y) := by
  apply Differentiable.fun_sum
  intro n _
  by_cases hn : n = 0
  · subst n
    simp
  · exact (differentiable_const _).div
      (differentiable_id.const_cpow (Or.inl (by exact_mod_cast hn)))
      (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn)))

theorem differentiableAt_f (y : ℝ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (f y) s :=
  ((differentiableAt_riemannZeta hs).mul (differentiable_Q y s)).sub_const 1

theorem differentiableAt_H (y : ℝ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (H y) s :=
  ((differentiableAt_f y hs).pow 2).const_sub 1

theorem continuous_vertical_F (y : ℝ) {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous (fun t : ℝ => F y ((σ : ℂ) + t * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : (σ : ℂ) + t * Complex.I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
      Complex.one_re] at this
    exact hσ this
  have hv : Continuous (fun t : ℝ => (σ : ℂ) + t * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact ((ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * Complex.I)
    (g := f y) (differentiableAt_f y hs).continuousAt hv.continuousAt).norm).pow 2

theorem intervalIntegrable_F (y u : ℝ) {σ : ℝ} (hσ : σ ≠ 1) :
    IntervalIntegrable (fun t : ℝ => F y ((σ : ℂ) + t * Complex.I)) volume (-u) u :=
  (continuous_vertical_F y hσ).intervalIntegrable _ _

theorem M_integrable_nonneg (y : ℝ) {σ : ℝ} (hσ : σ ≠ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable (fun t : ℝ => F y ((σ : ℂ) + t * Complex.I)) volume (-u) u ∧
      0 ≤ M y σ u := by
  refine ⟨intervalIntegrable_F y u hσ, ?_⟩
  apply intervalIntegral.integral_nonneg (by linarith)
  intro t _
  exact sq_nonneg _

end LiuWang.Proof.GlobalZeroDensity
