/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted and generalized for the Liu–Wang foundations project.

Source: MathExtras/NumberTheory/Vinogradov/CircleMethod.lean,
`integral_vonMangoldtExpSum_cube_kernel` (Gershon Bialer).
The proof below is reassembled from the existing integer-character integral;
no Bilinear module or external analytic assumptions are imported.
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma2PrimitiveLargeSieve
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Finite ternary circle-method identity

Three independently indexed finite integer spectra, with independent complex
weights, on any unit interval. Repeated frequencies are allowed. The natural
number specialization uses precisely `n ≤ N ∧ N ≤ 1000 * n` and von Mangoldt
weights. These are exact finite identities, not major-arc estimates, positivity
results, or a proof that a ternary prime representation exists.

Character convention: `charReal x = exp (2 * π * x * I)`.
-/

namespace LiuWang.Fourier

open Finset MeasureTheory AnalyticNumberTheory.LargeSieve
open scoped BigOperators Interval

noncomputable section

/-- A finite exponential sum; frequencies are integers, coefficients are complex.
The index type need not itself be an integer type, nor be injectively indexed. -/
def indexedExpSum {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ι → ℂ)
    (α : ℝ) : ℂ :=
  ∑ i ∈ s, b i * charReal ((f i : ℝ) * α)

/-- Exact extraction of a ternary coefficient from three independent finite
integer-frequency exponential sums. There are no analytic or counting inputs. -/
theorem integral_indexedExpSum_triple
    {ι κ ρ : Type*} (s : Finset ι) (t : Finset κ) (v : Finset ρ)
    (f : ι → ℤ) (g : κ → ℤ) (h : ρ → ℤ)
    (a : ι → ℂ) (b : κ → ℂ) (c : ρ → ℂ) (N : ℤ) (u : ℝ) :
    (∫ α in u..u + 1,
      indexedExpSum s f a α * indexedExpSum t g b α * indexedExpSum v h c α *
        charReal (-(N : ℝ) * α)) =
      ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ v,
        if f i + g j + h k = N then a i * b j * c k else 0 := by
  classical
  have hpoint (α : ℝ) :
      indexedExpSum s f a α * indexedExpSum t g b α * indexedExpSum v h c α *
          charReal (-(N : ℝ) * α) =
        ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ v,
          (a i * b j * c k) * charReal (((f i + g j + h k - N : ℤ) : ℝ) * α) := by
    unfold indexedExpSum
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs =>
      rw [Finset.sum_comm]
      arg 2
      ext j
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (((f i + g j + h k - N : ℤ) : ℝ) * α) =
      (f i : ℝ) * α + (g j : ℝ) * α + (h k : ℝ) * α + (-(N : ℝ) * α) by
        push_cast
        ring]
    simp only [charReal_add]
    ring
  rw [intervalIntegral.integral_congr (fun α _ => hpoint α)]
  have hint (i : ι) (j : κ) (k : ρ) :
      IntervalIntegrable (fun α : ℝ =>
        (a i * b j * c k) * charReal (((f i + g j + h k - N : ℤ) : ℝ) * α))
        volume u (u + 1) := by
    apply Continuous.intervalIntegrable
    unfold charReal
    fun_prop
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_finsetSum (fun k _ => hint i j k)]
      apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul, charReal_intervalIntegral_int]
      by_cases heq : f i + g j + h k = N
      · simp [heq]
      · simp [sub_ne_zero.mpr heq, heq]
    · intro j hj
      refine (continuous_finsetSum _ (fun k _ => ?_)).intervalIntegrable _ _
      unfold charReal
      fun_prop
  · intro i hi
    refine (continuous_finsetSum _ (fun j _ =>
      continuous_finsetSum _ (fun k _ => ?_))).intervalIntegrable _ _
    unfold charReal
    fun_prop

/-- Direct `Finset ℤ` API: all three spectra and all three weights are independent. -/
theorem integral_finiteExpSum_triple
    (s t v : Finset ℤ) (a b c : ℤ → ℂ) (N : ℤ) (u : ℝ) :
    (∫ α in u..u + 1,
      (∑ i ∈ s, a i * charReal ((i : ℝ) * α)) *
      (∑ j ∈ t, b j * charReal ((j : ℝ) * α)) *
      (∑ k ∈ v, c k * charReal ((k : ℝ) * α)) *
        charReal (-(N : ℝ) * α)) =
      ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ v,
        if i + j + k = N then a i * b j * c k else 0 :=
  integral_indexedExpSum_triple s t v id id id a b c N u

/-- The Liu–Wang lower cutoff without rounding or rational coercion:
`n ≤ N` and `1000 * n ≥ N`, including both endpoints. -/
def liuWangSupport (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => N ≤ 1000 * n)

@[simp] theorem mem_liuWangSupport (N n : ℕ) :
    n ∈ liuWangSupport N ↔ n ≤ N ∧ N ≤ 1000 * n := by
  simp [liuWangSupport]

/-- Lower-truncated von Mangoldt sum, with natural indices and integer frequencies. -/
def liuWangExpSum (N : ℕ) (α : ℝ) : ℂ :=
  indexedExpSum (liuWangSupport N) (fun n => (n : ℤ))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) α

/-- Actual weighted ternary sum, not a black-box representation-count input. -/
def liuWangTernarySum (N : ℕ) : ℝ :=
  ∑ i ∈ liuWangSupport N, ∑ j ∈ liuWangSupport N, ∑ k ∈ liuWangSupport N,
    if i + j + k = N then
      ArithmeticFunction.vonMangoldt i * ArithmeticFunction.vonMangoldt j *
        ArithmeticFunction.vonMangoldt k else 0

/-- Exact Liu–Wang lower-truncated Λ-weighted ternary circle identity on any
unit interval. The result is the complex embedding of the real weighted sum. -/
theorem integral_liuWangExpSum_cube (N : ℕ) (u : ℝ) :
    (∫ α in u..u + 1, liuWangExpSum N α ^ 3 * charReal (-(N : ℝ) * α)) =
      (liuWangTernarySum N : ℂ) := by
  have H := integral_indexedExpSum_triple
    (liuWangSupport N) (liuWangSupport N) (liuWangSupport N)
    (fun n : ℕ => (n : ℤ)) (fun n : ℕ => (n : ℤ)) (fun n : ℕ => (n : ℤ))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (N : ℤ) u
  simpa only [liuWangExpSum, liuWangTernarySum, pow_succ, pow_zero, one_mul,
    Int.cast_natCast, ← Nat.cast_add, Nat.cast_inj, Complex.ofReal_sum,
    Complex.ofReal_mul, apply_ite Complex.ofReal, Complex.ofReal_zero] using H

end
end LiuWang.Fourier
