import LiuWang.Proof.Campaign20260915.Totient.NuArithmetic

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Totient

theorem totient_prime_pow_ratio {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((p ^ (k + 1) : ℕ) : ℝ) / ((p ^ (k + 1)).totient : ℝ) =
      (p : ℝ) / ((p : ℝ) - 1) := by
  rw [Nat.totient_prime_pow_succ hp]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  rw [pow_succ, mul_div_mul_left _ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))]

theorem totient_ratio_le_nu_prime_power {p k : ℕ} (hp : p.Prime)
    (hq : 3 ≤ p ^ k) :
    ((p ^ k : ℕ) : ℝ) / ((p ^ k).totient : ℝ) ≤ nu (p ^ k) := by
  cases k with
  | zero => norm_num at hq
  | succ k =>
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      calc
        _ = (p : ℝ) / ((p : ℝ) - 1) := totient_prime_pow_ratio hp k
        _ ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
        _ ≤ _ := two_le_nu (by exact_mod_cast hq)

end LiuWang.Proof.Campaign20260915.Totient
