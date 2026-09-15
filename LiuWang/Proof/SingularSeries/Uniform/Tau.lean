import LiuWang.Proof.SingularSeries.Uniform.Reciprocal

/-! The sixfold Dirichlet convolution of zeta and its finite square-weighted mass. -/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace LiuWang.Proof.SingularSeries.Uniform

def tau (k : ℕ) : ArithmeticFunction ℝ := (ζ : ArithmeticFunction ℝ) ^ k

theorem tau_multiplicative (k : ℕ) : (tau k).IsMultiplicative :=
  isMultiplicative_zeta.natCast.pow

theorem tau_one (k : ℕ) : tau k 1 = 1 := (tau_multiplicative k).map_one

theorem zeta_real_apply {n : ℕ} (hn : n ≠ 0) : (ζ : ArithmeticFunction ℝ) n = 1 := by
  simp [zeta_apply_ne hn]

theorem tau_nonneg (k n : ℕ) : 0 ≤ tau k n := by
  induction k generalizing n with
  | zero => simp [tau, one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [tau, pow_succ]
    exact convolution_nonneg ih (fun n => by simp only [natCoe_apply]; positivity) n

theorem convolution_prime (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    (f * g) p = f 1 * g p + f p * g 1 := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d e => f d * g e)]
  have h := Nat.sum_divisors_prime_pow (k := 1) (f := fun d => f d * g (p / d)) hp
  rw [pow_one] at h
  rw [show 1 + 1 = Nat.succ (Nat.succ 0) from rfl,
    Finset.sum_range_succ, Finset.sum_range_succ, sum_range_zero] at h
  simpa only [pow_one, pow_zero, Nat.div_one, Nat.div_self hp.pos, zero_add] using h

theorem tau_prime (k : ℕ) {p : ℕ} (hp : p.Prime) : tau k p = k := by
  induction k with
  | zero => simp [tau, one_apply_ne hp.ne_one]
  | succ k ih =>
    change ((tau k) * (ζ : ArithmeticFunction ℝ)) p = _
    rw [convolution_prime _ _ hp, tau_one, zeta_real_apply hp.ne_zero,
      zeta_real_apply one_ne_zero, ih]
    push_cast
    ring

theorem squareSum_zeta_le (X : ℕ) : squareSum (ζ : ArithmeticFunction ℝ) X ≤ 5 / 3 := by
  have he : squareSum (ζ : ArithmeticFunction ℝ) X =
      ∑ n ∈ Icc 1 X, 1 / (n : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro n hn
    rw [zeta_real_apply (Nat.ne_of_gt (mem_Icc.mp hn).1)]
  rw [he]
  exact reciprocal_square_prefix X

theorem squareSum_tau_le (k X : ℕ) : squareSum (tau k) X ≤ (5 / 3 : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [tau, pow_zero, squareSum, one_apply, ite_div, zero_div]
    by_cases hX : 1 ≤ X <;> simp [hX]
  | succ k ih =>
    change squareSum (tau k * (ζ : ArithmeticFunction ℝ)) X ≤ _
    calc
      _ ≤ squareSum (tau k) X * squareSum (ζ : ArithmeticFunction ℝ) X :=
        squareSum_convolution_le (tau_nonneg k) (fun n => by simp only [natCoe_apply]; positivity) X
      _ ≤ (5 / 3 : ℝ) ^ k * (5 / 3) :=
        mul_le_mul ih (squareSum_zeta_le X)
          (squareSum_nonneg (fun n => by simp only [natCoe_apply]; positivity) X) (by positivity)
      _ = _ := (pow_succ _ _).symm

theorem squareSum_tau_six_lt (X : ℕ) : squareSum (tau 6) X < 22 :=
  (squareSum_tau_le 6 X).trans_lt reciprocal_square_sixth_constant

end LiuWang.Proof.SingularSeries.Uniform
