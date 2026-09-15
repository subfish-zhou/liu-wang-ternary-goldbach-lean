import LiuWang.Proof.NonprincipalDensityAdvance.Family
import AnalyticNumberTheory.LargeSieve.Multiplicative

/-!
# Exact fixed-level character energy with the principal part removed

This finite orthogonality input is not a hybrid large sieve or a vertical
L-function mean. It applies to all characters at the original modulus, even
when the coefficient support is longer than a complete residue system.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.NonprincipalDensityAdvance

def residuePolynomial {q : ℕ} [NeZero q] (chi : Character q) (b : ZMod q → ℂ) : ℂ :=
  ∑ x : ZMod q, b x * chi x

theorem residue_energy (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    (∑ chi : Character q, ‖residuePolynomial chi b‖ ^ 2) =
      (q.totient : ℝ) * ∑ x : ZMod q, if IsUnit x then ‖b x‖ ^ 2 else 0 := by
  have he :
      (∑ chi : Character q, (‖residuePolynomial chi b‖ : ℂ) ^ 2) =
        (q.totient : ℂ) * ∑ x : ZMod q, if IsUnit x then (‖b x‖ : ℂ) ^ 2 else 0 := by
    calc
      _ = ∑ chi : Character q, ∑ x : ZMod q, ∑ y : ZMod q,
          (b x * chi x) * star (b y * chi y) := by
        apply sum_congr rfl
        intro chi _
        exact normSq_sum_eq_sum_mul_star univ (fun x => b x * chi x)
      _ = ∑ x : ZMod q, ∑ y : ZMod q, b x * star (b y) *
          (∑ chi : Character q, chi x * star (chi y)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        rw [sum_comm]
        apply sum_congr rfl
        intro y _
        rw [mul_sum]
        apply sum_congr rfl
        intro chi _
        rw [star_mul]
        ring
      _ = ∑ x : ZMod q, ∑ y : ZMod q, b x * star (b y) *
          (if IsUnit x ∧ IsUnit y ∧ x = y then (q.totient : ℂ) else 0) := by
        apply sum_congr rfl
        intro x _
        apply sum_congr rfl
        intro y _
        have hc := charOrthSum (Nat.pos_of_ne_zero (NeZero.ne q)) x y
        by_cases hx : IsUnit x <;> by_cases hy : IsUnit y <;> by_cases hxy : x = y <;>
          simp [hx, hy, hxy] at hc ⊢ <;> simp [hc]
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        by_cases hx : IsUnit x
        · rw [if_pos hx]
          rw [sum_eq_single x]
          · simp only [hx, and_self, ite_true]
            rw [mul_comm, ← Complex.ofReal_pow, Complex.sq_norm, ← Complex.mul_conj]
            rfl
          · intro y _ hy
            simp only [show x ≠ y from Ne.symm hy, and_false, ite_false, mul_zero]
          · simp
        · simp [hx]
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, ← Complex.ofReal_pow, Complex.ofReal_re, apply_ite,
    Complex.zero_re] using hr

def characterPolynomial {q : ℕ} (chi : Character q) (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S, a n * chi n

def residueCoefficient {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ) (x : ZMod q) : ℂ :=
  ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = x), a n

theorem characterPolynomial_eq_residuePolynomial {q : ℕ} [NeZero q]
    (chi : Character q) (S : Finset ℕ) (a : ℕ → ℂ) :
    characterPolynomial chi S a = residuePolynomial chi (residueCoefficient S a) := by
  unfold characterPolynomial residuePolynomial residueCoefficient
  rw [← sum_fiberwise (s := S) (g := fun n : ℕ => (n : ZMod q))
    (f := fun n => a n * chi n)]
  apply sum_congr rfl
  intro x _
  rw [sum_mul]
  apply sum_congr rfl
  intro n hn
  rw [(mem_filter.mp hn).2]

theorem normalized_nonprincipal_energy (q : ℕ) [NeZero q]
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ chi ∈ nonprincipalCharacters q, ‖characterPolynomial chi S a‖ ^ 2) / q.totient =
      (∑ x : ZMod q, if IsUnit x then ‖residueCoefficient S a x‖ ^ 2 else 0) -
        ‖characterPolynomial (1 : Character q) S a‖ ^ 2 / q.totient := by
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have he := residue_energy q (residueCoefficient S a)
  simp_rw [← characterPolynomial_eq_residuePolynomial] at he
  rw [← sum_erase_add _ _ (mem_univ (1 : Character q))] at he
  change (∑ chi ∈ nonprincipalCharacters q, ‖characterPolynomial chi S a‖ ^ 2) +
    ‖characterPolynomial (1 : Character q) S a‖ ^ 2 = _ at he
  apply (eq_sub_iff_add_eq).mpr
  rw [← add_div, he, mul_div_cancel_left₀ _ hphi]

theorem normalized_nonprincipal_energy_le (q : ℕ) [NeZero q]
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ chi ∈ nonprincipalCharacters q, ‖characterPolynomial chi S a‖ ^ 2) / q.totient ≤
      ∑ x : ZMod q, if IsUnit x then ‖residueCoefficient S a x‖ ^ 2 else 0 := by
  rw [normalized_nonprincipal_energy]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

theorem normalized_Q_energy (q : ℕ) [NeZero q] (X : ℝ) (s : ℂ) :
    (∑ chi ∈ nonprincipalCharacters q, ‖Q chi X s‖ ^ 2) / q.totient =
      (∑ x : ZMod q, if IsUnit x then
        ‖residueCoefficient (range ⌈X⌉₊)
          (fun n => (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s) x‖ ^ 2 else 0) -
        ‖Q (1 : Character q) X s‖ ^ 2 / q.totient := by
  have he (chi : Character q) :
      characterPolynomial chi (range ⌈X⌉₊)
        (fun n => (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s) = Q chi X s := by
    apply sum_congr rfl
    intro n _
    dsimp [twistedMu]
    ring
  simpa only [he] using normalized_nonprincipal_energy q (range ⌈X⌉₊)
    (fun n => (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s)

end LiuWang.Proof.NonprincipalDensityAdvance
