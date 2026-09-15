import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace LiuWang.Proof.Campaign20260915.Density

def divisorMobiusMass : ArithmeticFunction ℝ :=
  (ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) (μ : ArithmeticFunction ℝ)) *
    (ζ : ArithmeticFunction ℝ)

theorem divisorMobiusMass_multiplicative : divisorMobiusMass.IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).mul
    isMultiplicative_zeta.natCast

theorem divisorMobiusMass_eq (n : ℕ) :
    divisorMobiusMass n = ∑ a ∈ n.divisors, |(μ a : ℝ)| := by
  rw [divisorMobiusMass, coe_mul_zeta_apply]
  apply sum_congr rfl
  intro a _
  simp only [pmul_apply, intCoe_apply]
  rcases moebius_eq_or a with h | h | h <;> rw [h] <;> norm_num

theorem divisorMobiusMass_nonneg (n : ℕ) : 0 ≤ divisorMobiusMass n := by
  rw [divisorMobiusMass_eq]
  exact sum_nonneg (fun _ _ => abs_nonneg _)

theorem divisorMobiusMass_prime_power {p k : ℕ} (hp : p.Prime) :
    divisorMobiusMass (p ^ (k + 1)) = 2 := by
  rw [divisorMobiusMass_eq, Nat.sum_divisors_prime_pow hp, sum_range_succ']
  have he (i : ℕ) : |(μ (p ^ (i + 1)) : ℝ)| = if i = 0 then 1 else 0 := by
    rw [moebius_apply_prime_pow hp (by omega)]
    by_cases hi : i = 0 <;> simp [hi]
  simp_rw [he]
  norm_num

theorem prime_mobius_totient_scalar {p : ℝ} (hp : 2 ≤ p) :
    4 * (p - 1) ^ 2 ≤ p ^ 3 := by
  have h : 0 ≤ (p - 2) ^ 3 + 2 * (p - 2) ^ 2 + 4 * (p - 2) + 4 := by
    have : 0 ≤ p - 2 := by linarith
    positivity
  nlinarith only [h]

theorem divisorMobiusMass_totient_square (n : ℕ) :
    (divisorMobiusMass n) ^ 2 * (n.totient : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p k hp =>
    cases k with
    | zero => simp [divisorMobiusMass]
    | succ k =>
      rw [divisorMobiusMass_prime_power hp, Nat.totient_prime_pow_succ hp]
      push_cast [hp.one_lt.le]
      have hpR : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp.two_le
      have h := mul_le_mul_of_nonneg_left (prime_mobius_totient_scalar hpR)
        (sq_nonneg ((p : ℝ) ^ k))
      have hk : (1 : ℝ) ≤ (p : ℝ) ^ k := one_le_pow₀ (by linarith)
      have hs : ((p : ℝ) ^ k) ^ 2 ≤ ((p : ℝ) ^ k) ^ 3 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ (p : ℝ) ^ 3 by positivity)
      rw [pow_succ (p : ℝ) k]
      nlinarith only [h, hm]
  | coprime a b _ _ hab ha hb =>
    rw [divisorMobiusMass_multiplicative.map_mul_of_coprime hab, Nat.totient_mul hab]
    push_cast
    have h := mul_le_mul ha hb (by positivity) (by positivity)
    nlinarith only [h]

theorem totient_multiple_le (d e : ℕ) : (d * e).totient ≤ d * e.totient := by
  induction d using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul p d hp ih =>
    rw [mul_assoc]
    have h : (p * (d * e)).totient ≤ p * (d * e).totient := by
      by_cases hd : p ∣ d * e
      · rw [Nat.totient_mul_of_prime_of_dvd hp hd]
      · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd]
        exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
    exact h.trans ((Nat.mul_le_mul_left p ih).trans_eq (by ring))

theorem divisorMobiusMass_totient_compensation (d e : ℕ) :
    divisorMobiusMass e * ((d * e).totient : ℝ) ≤ (d * e : ℕ) * Real.sqrt e := by
  have ht : ((d * e).totient : ℝ) ≤ (d : ℝ) * e.totient :=
    by exact_mod_cast totient_multiple_le d e
  have ht2 := pow_le_pow_left₀ (Nat.cast_nonneg (d * e).totient) ht 2
  have h1 := mul_le_mul_of_nonneg_left ht2 (sq_nonneg (divisorMobiusMass e))
  have h2 := mul_le_mul_of_nonneg_left (divisorMobiusMass_totient_square e)
    (sq_nonneg (d : ℝ))
  have hs := Real.sq_sqrt (Nat.cast_nonneg e)
  have h0 := divisorMobiusMass_nonneg e
  have hR : 0 ≤ (d : ℝ) * e * Real.sqrt e := by positivity
  have he : ((d : ℝ) * e * Real.sqrt e) ^ 2 = (d : ℝ) ^ 2 * (e : ℝ) ^ 3 := by
    rw [mul_pow, mul_pow, hs]
    ring
  have hL : (divisorMobiusMass e * ((d * e).totient : ℝ)) ^ 2 ≤
      (d : ℝ) ^ 2 * (e : ℝ) ^ 3 := by nlinarith only [h1, h2]
  push_cast
  nlinarith only [hL, he, hR]

#print axioms divisorMobiusMass_totient_compensation

end LiuWang.Proof.Campaign20260915.Density
