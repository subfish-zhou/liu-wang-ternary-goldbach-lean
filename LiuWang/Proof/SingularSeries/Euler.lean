import LiuWang.Proof.SingularSeries.Convergence
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# The ternary Euler product

The product is proved equal to the absolutely convergent original series.
The positivity theorem is qualitative; it does not assert the decimal
lower bound `0.6601` for the universal odd-prime product.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Topology

namespace LiuWang.Proof.SingularSeries

def realCoefficient (N q : ℕ) : ℝ :=
  (ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) ^ 3 * (ramanujan N q).re

theorem ofReal_realCoefficient (N q : ℕ) :
    (realCoefficient N q : ℂ) = coefficient N q :=
  (coefficient_eq_real N q).symm

@[simp] theorem realCoefficient_zero (N : ℕ) : realCoefficient N 0 = 0 := by
  apply Complex.ofReal_injective
  simp only [ofReal_realCoefficient, coefficient_zero, Complex.ofReal_zero]

@[simp] theorem realCoefficient_one (N : ℕ) : realCoefficient N 1 = 1 := by
  apply Complex.ofReal_injective
  simp only [ofReal_realCoefficient, coefficient_one, Complex.ofReal_one]

theorem realCoefficient_mul (N : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    realCoefficient N (a * b) = realCoefficient N a * realCoefficient N b := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, ofReal_realCoefficient, coefficient_mul N hab]

theorem realCoefficient_norm_summable {N : ℕ} (hN : 0 < N) :
    Summable (fun q => ‖realCoefficient N q‖) := by
  simpa only [← ofReal_realCoefficient, Complex.norm_real, Real.norm_eq_abs] using
    coefficient_norm_summable hN

theorem realCoefficient_summable {N : ℕ} (hN : 0 < N) :
    Summable (realCoefficient N) := (realCoefficient_norm_summable hN).of_norm

def localFactor (N p : ℕ) : ℝ :=
  if p ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2
  else 1 + 1 / ((p : ℝ) - 1) ^ 3

theorem localFactor_eq_one_add (N : ℕ) {p : ℕ} (hp : p.Prime) :
    localFactor N p = 1 + realCoefficient N p := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_add, ofReal_realCoefficient, coefficient_prime N hp]
  unfold localFactor
  split_ifs <;> push_cast <;> ring

theorem realCoefficient_prime_power (N : ℕ) {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    realCoefficient N (p ^ k) = 0 := by
  apply Complex.ofReal_injective
  simp only [ofReal_realCoefficient, coefficient_prime_power N hp hk, Complex.ofReal_zero]

theorem localFactor_eq_prime_power_sum (N : ℕ) {p : ℕ} (hp : p.Prime) :
    localFactor N p = ∑' k : ℕ, realCoefficient N (p ^ k) := by
  rw [tsum_eq_sum (s := {0, 1}) (fun k hk =>
    realCoefficient_prime_power N hp (by simp only [mem_insert, mem_singleton] at hk; omega))]
  simp [localFactor_eq_one_add N hp]

def series (N : ℕ) : ℝ := ∑' q : ℕ, realCoefficient N q

theorem ofReal_series (N : ℕ) : (series N : ℂ) = ∑' q : ℕ, coefficient N q := by
  simp only [series, Complex.ofReal_tsum, ofReal_realCoefficient]

theorem euler_hasProd {N : ℕ} (hN : 0 < N) :
    HasProd (fun p : Nat.Primes => localFactor N p) (series N) := by
  have he : (fun p : Nat.Primes => localFactor N p) =
      (fun p : Nat.Primes => ∑' k : ℕ, realCoefficient N ((p : ℕ) ^ k)) :=
    funext fun p => localFactor_eq_prime_power_sum N p.property
  rw [he]
  exact EulerProduct.eulerProduct_hasProd (realCoefficient_one N)
    (fun {_ _} h => realCoefficient_mul N h)
    (realCoefficient_norm_summable hN) (realCoefficient_zero N)

theorem series_eq_eulerProduct {N : ℕ} (hN : 0 < N) :
    series N = ∏' p : Nat.Primes,
      (if (p : ℕ) ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2
       else 1 + 1 / ((p : ℝ) - 1) ^ 3) :=
  (euler_hasProd hN).tprod_eq.symm

theorem original_series_eq_eulerProduct {N : ℕ} (hN : 0 < N) :
    (∑' q : ℕ, coefficient N q) =
      ((∏' p : Nat.Primes,
        (if (p : ℕ) ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2
         else 1 + 1 / ((p : ℝ) - 1) ^ 3) : ℝ) : ℂ) := by
  rw [← ofReal_series, series_eq_eulerProduct hN]

theorem localFactor_two_of_odd {N : ℕ} (hN : Odd N) : localFactor N 2 = 2 := by
  have h2 : ¬ 2 ∣ N := by
    obtain ⟨k, hk⟩ := hN
    rintro ⟨m, hm⟩
    omega
  norm_num [localFactor, h2]

theorem localFactor_pos_of_odd {N p : ℕ} (hN : Odd N) (hp : p.Prime) :
    0 < localFactor N p := by
  by_cases h2 : p = 2
  · subst p
    rw [localFactor_two_of_odd hN]
    norm_num
  have hp3 : (3 : ℝ) ≤ p := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    exact_mod_cast hp3
  unfold localFactor
  split_ifs
  · have hd : 1 < ((p : ℝ) - 1) ^ 2 := by nlinarith
    have h := (div_lt_one (by positivity : 0 < ((p : ℝ) - 1) ^ 2)).mpr hd
    linarith
  · have hp1 : 0 < (p : ℝ) - 1 := by linarith
    positivity

theorem series_pos_of_odd {N : ℕ} (hN : Odd N) : 0 < series N := by
  have hN0 : 0 < N := by obtain ⟨k, hk⟩ := hN; omega
  have hprod := euler_hasProd hN0
  have hnonneg : 0 ≤ series N := by
    apply ge_of_tendsto hprod
    exact Filter.Eventually.of_forall fun s =>
      prod_nonneg fun p _ => (localFactor_pos_of_odd hN p.property).le
  have hne : series N ≠ 0 := by
    rw [← hprod.tprod_eq]
    have he : (fun p : Nat.Primes => localFactor N p) =
        (fun p : Nat.Primes => 1 + realCoefficient N p) :=
      funext fun p => localFactor_eq_one_add N p.property
    rw [he]
    apply tprod_one_add_ne_zero_of_summable
    · intro p
      rw [← localFactor_eq_one_add N p.property]
      exact (localFactor_pos_of_odd hN p.property).ne'
    · exact (realCoefficient_norm_summable hN0).comp_injective
        (show Function.Injective (fun p : Nat.Primes => (p : ℕ)) from Subtype.val_injective)
  exact lt_of_le_of_ne hnonneg hne.symm

end LiuWang.Proof.SingularSeries
