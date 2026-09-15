import LiuWang.Proof.SourceRoute.SecondArc.Continuation.GaussianPayment

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment

def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13}

def primeFactor (p : ℕ) : ℝ := (p : ℝ) ^ (32 : ℕ) / ((p : ℝ) - 1) ^ (33 : ℕ)

def correction (n : ℕ) : ℝ :=
  ∏ p ∈ smallPrimes, if p ∣ n then primeFactor p else 1

def correctionConstant : ℝ := (30030 : ℝ) ^ (32 : ℕ) / (5760 : ℝ) ^ (33 : ℕ)

theorem smallPrimes_prime {p : ℕ} (hp : p ∈ smallPrimes) : p.Prime := by
  simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem primeFactor_ge_one {p : ℕ} (hp : p ∈ smallPrimes) : 1 ≤ primeFactor p := by
  simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [primeFactor]

theorem correction_product : (∏ p ∈ smallPrimes, primeFactor p) = correctionConstant := by
  norm_num [smallPrimes, primeFactor, correctionConstant]

theorem correction_factor_bounds (n : ℕ) {p : ℕ} (hp : p ∈ smallPrimes) :
    1 ≤ (if p ∣ n then primeFactor p else 1) ∧
      (if p ∣ n then primeFactor p else 1) ≤ primeFactor p := by
  split_ifs <;> exact ⟨by simp_all [primeFactor_ge_one hp], by simp_all [primeFactor_ge_one hp]⟩

theorem correction_bounds (n : ℕ) : 1 ≤ correction n ∧ correction n ≤ correctionConstant := by
  constructor
  · exact Finset.one_le_prod (fun p hp => (correction_factor_bounds n hp).1)
  · rw [← correction_product]
    exact Finset.prod_le_prod
      (fun p hp => le_trans (by norm_num) (correction_factor_bounds n hp).1)
      (fun p hp => (correction_factor_bounds n hp).2)

theorem prime_divisor_factor_mul {p a b : ℕ} (c : ℝ)
    (hp : p.Prime) (hab : a.Coprime b) :
    (if p ∣ a * b then c else 1) =
      (if p ∣ a then c else 1) * (if p ∣ b then c else 1) := by
  have hn : ¬ (p ∣ a ∧ p ∣ b) := by
    rintro ⟨ha, hb⟩
    exact hp.not_dvd_one (hab ▸ Nat.dvd_gcd ha hb)
  simp only [hp.dvd_mul]
  split_ifs <;> simp_all

theorem correction_mul {a b : ℕ} (hab : a.Coprime b) :
    correction (a * b) = correction a * correction b := by
  unfold correction
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl
    (fun p hp => prime_divisor_factor_mul (primeFactor p) (smallPrimes_prime hp) hab)

theorem correction_pow {p k : ℕ} (hk : 0 < k) :
    correction (p ^ k) = correction p := by
  apply Finset.prod_congr rfl
  intro a ha
  have he : a ∣ p ^ k ↔ a ∣ p :=
    ⟨(smallPrimes_prime ha).dvd_of_dvd_pow, fun h => dvd_pow h hk.ne'⟩
  simp only [he]

theorem large_prime_power_bound {p : ℕ} (hp : 17 ≤ p) :
    p ^ (32 : ℕ) ≤ (p - 1) ^ (33 : ℕ) := by
  have h := Nat.pow_le_pow_left (show 16 * p ≤ 17 * (p - 1) by omega) 32
  rw [mul_pow, mul_pow] at h
  have hbase : 17 ^ (32 : ℕ) ≤ 16 ^ (32 : ℕ) * (p - 1) := by
    calc
      17 ^ (32 : ℕ) ≤ 16 ^ (33 : ℕ) := by norm_num
      _ = 16 ^ (32 : ℕ) * 16 := by rw [pow_succ]
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hm := Nat.mul_le_mul_right ((p - 1) ^ (32 : ℕ)) hbase
  have ht : 16 ^ (32 : ℕ) * p ^ (32 : ℕ) ≤
      16 ^ (32 : ℕ) * (p - 1) ^ (33 : ℕ) := by
    apply (h.trans hm).trans_eq
    rw [pow_succ]
    ac_rfl
  exact Nat.le_of_mul_le_mul_left ht (by norm_num)

theorem prime_small_or_large {p : ℕ} (hp : p.Prime) :
    p ∈ smallPrimes ∨ 17 ≤ p := by
  by_cases hl : 17 ≤ p
  · exact Or.inr hl
  · left
    have hp2 := hp.two_le
    interval_cases p <;> norm_num [smallPrimes] at *

theorem primeFactor_le_correction {p : ℕ} (hp : p ∈ smallPrimes) :
    primeFactor p ≤ correction p := by
  simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [correction, smallPrimes, primeFactor]

theorem prime_power_correction {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ (32 : ℕ) ≤ correction p * ((p : ℝ) - 1) ^ (33 : ℕ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rcases prime_small_or_large hp with hs | hl
  · have h := mul_le_mul_of_nonneg_right (primeFactor_le_correction hs)
      (by positivity : 0 ≤ ((p : ℝ) - 1) ^ (33 : ℕ))
    rw [primeFactor, div_mul_cancel₀ _ (by positivity)] at h
    exact h
  · have ht : (p : ℝ) ^ (32 : ℕ) ≤ ((p : ℝ) - 1) ^ (33 : ℕ) := by
      have h := (Nat.cast_le (α := ℝ)).mpr (large_prime_power_bound hl)
      simpa only [Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one] using h
    exact ht.trans (le_mul_of_one_le_left (by positivity) (correction_bounds p).1)

theorem fixed_correction_budget :
    correctionConstant * (3100 : ℝ) ^ (3 : ℕ) < (8 : ℝ) ^ (33 : ℕ) := by
  norm_num [correctionConstant]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment
