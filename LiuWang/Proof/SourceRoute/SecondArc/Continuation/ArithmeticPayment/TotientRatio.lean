import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.PrimeCorrection

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment

theorem totient_power_local (n : ℕ) :
    (n : ℝ) ^ (32 : ℕ) ≤ correction n * (n.totient : ℝ) ^ (33 : ℕ) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => norm_num [correction, smallPrimes]
  | prime_pow p k hp hk =>
    rw [correction_pow hk, Nat.totient_prime_pow hp hk]
    have he : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one,
      mul_pow, mul_pow]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have ha : 1 ≤ (p : ℝ) ^ (k - 1) := one_le_pow₀ hp1
    have hpow : ((p : ℝ) ^ (k - 1)) ^ (32 : ℕ) ≤
        ((p : ℝ) ^ (k - 1)) ^ (33 : ℕ) := pow_le_pow_right₀ ha (by norm_num)
    calc
      _ ≤ ((p : ℝ) ^ (k - 1)) ^ (33 : ℕ) *
          (correction p * ((p : ℝ) - 1) ^ (33 : ℕ)) :=
        mul_le_mul hpow (prime_power_correction hp) (by positivity) (by positivity)
      _ = _ := by ring
  | coprime a b _ _ hab ha hb =>
    rw [correction_mul hab, Nat.totient_mul hab, Nat.cast_mul, Nat.cast_mul, mul_pow, mul_pow]
    exact (mul_le_mul ha hb (by positivity)
      (mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (correction_bounds a).1)
        (by positivity))).trans_eq (by ring)

theorem totient_power (n : ℕ) :
    (n : ℝ) ^ (32 : ℕ) ≤ correctionConstant * (n.totient : ℝ) ^ (33 : ℕ) :=
  (totient_power_local n).trans
    (mul_le_mul_of_nonneg_right (correction_bounds n).2 (by positivity))

theorem totient_ratio_power {q : ℕ} (hq : 0 < q) :
    ((q : ℝ) / (q.totient : ℝ)) ^ (33 : ℕ) ≤ correctionConstant * (q : ℝ) := by
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  rw [div_pow]
  apply (div_le_iff₀ (by positivity : 0 < (q.totient : ℝ) ^ (33 : ℕ))).mpr
  calc
    (q : ℝ) ^ (33 : ℕ) = (q : ℝ) ^ (32 : ℕ) * (q : ℝ) := by rw [pow_succ]
    _ ≤ (correctionConstant * (q.totient : ℝ) ^ (33 : ℕ)) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right (totient_power q) (Nat.cast_nonneg q)
    _ = _ := by ring

theorem source_power_budget {L : ℝ} (hL : 3100 ≤ L) :
    correctionConstant * L ^ (3 : ℕ) ≤ (8 * L / 3100) ^ (33 : ℕ) := by
  let t := L / 3100
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have hLt : L = 3100 * t := by dsimp [t]; ring
  have hpow : t ^ (3 : ℕ) ≤ t ^ (33 : ℕ) := pow_le_pow_right₀ ht (by norm_num)
  calc
    correctionConstant * L ^ (3 : ℕ) =
        (correctionConstant * (3100 : ℝ) ^ (3 : ℕ)) * t ^ (3 : ℕ) := by
      rw [hLt, mul_pow]
      ring
    _ ≤ (8 : ℝ) ^ (33 : ℕ) * t ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right fixed_correction_budget.le (by positivity)
    _ ≤ (8 : ℝ) ^ (33 : ℕ) * t ^ (33 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = _ := by rw [← mul_pow]; congr 1; dsimp [t]; ring

theorem totient_ratio_le_source {q : ℕ} (hq : 0 < q) {L : ℝ}
    (hL : 3100 ≤ L) (hqL : (q : ℝ) ≤ L ^ (3 : ℕ)) :
    (q : ℝ) / (q.totient : ℝ) ≤ 8 * L / 3100 := by
  have hc : 0 ≤ correctionConstant := by norm_num [correctionConstant]
  have hp := (totient_ratio_power hq).trans
    ((mul_le_mul_of_nonneg_left hqL hc).trans (source_power_budget hL))
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (33 : ℕ) ≠ 0)).mp hp

theorem totient_ratio_le_scaling {q : ℕ} (hq : 0 < q) {L : ℝ}
    (hL : 3100 ≤ L) (hqL : (q : ℝ) ≤ L ^ (3 : ℕ)) :
    (q : ℝ) / (q.totient : ℝ) ≤ 8 * scaling L ^ (2 : ℕ) := by
  apply (totient_ratio_le_source hq hL hqL).trans_eq
  have hs := (scaling_bounds hL).2
  linarith

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment
