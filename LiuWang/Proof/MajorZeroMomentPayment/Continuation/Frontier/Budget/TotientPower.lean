import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.SourceTotal

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget

def smallPrimeCorrection (n : ℕ) : ℕ :=
  (if 2 ∣ n then 128 else 1)*(if 3 ∣ n then 9 else 1)*(if 5 ∣ n then 2 else 1)

theorem prime_divisor_factor_mul {p a b c : ℕ} (hp : p.Prime) (hab : a.Coprime b) :
    (if p ∣ a*b then c else 1) =
      (if p ∣ a then c else 1)*(if p ∣ b then c else 1) := by
  have hn : ¬ (p ∣ a ∧ p ∣ b) := by
    rintro ⟨ha, hb⟩
    exact hp.not_dvd_one (hab ▸ Nat.dvd_gcd ha hb)
  simp only [hp.dvd_mul]
  split_ifs <;> simp_all

theorem smallPrimeCorrection_mul {a b : ℕ} (hab : a.Coprime b) :
    smallPrimeCorrection (a*b) = smallPrimeCorrection a*smallPrimeCorrection b := by
  unfold smallPrimeCorrection
  rw [prime_divisor_factor_mul Nat.prime_two hab,
    prime_divisor_factor_mul (by norm_num : Nat.Prime 3) hab,
    prime_divisor_factor_mul (by norm_num : Nat.Prime 5) hab]
  ring

theorem smallPrimeCorrection_pow {p k : ℕ} (hk : 0 < k) :
    smallPrimeCorrection (p^k) = smallPrimeCorrection p := by
  have he (a : ℕ) (ha : a.Prime) : a ∣ p^k ↔ a ∣ p :=
    ⟨ha.dvd_of_dvd_pow, fun h => dvd_pow h hk.ne'⟩
  simp only [smallPrimeCorrection, he 2 Nat.prime_two,
    he 3 (by norm_num), he 5 (by norm_num)]

theorem smallPrimeCorrection_bounds (n : ℕ) :
    1 ≤ smallPrimeCorrection n ∧ smallPrimeCorrection n ≤ 2304 := by
  unfold smallPrimeCorrection
  split_ifs <;> norm_num

theorem prime_seven_eighth {p : ℕ} (hp : p.Prime) :
    p^7 ≤ smallPrimeCorrection p*(p-1)^8 := by
  by_cases hsmall : p < 7
  · interval_cases p <;> norm_num [smallPrimeCorrection]
    norm_num at hp
  have hp7 : 7 ≤ p := by omega
  have h := Nat.pow_le_pow_left (show 6*p ≤ 7*(p-1) by omega) 7
  rw [mul_pow, mul_pow] at h
  have ha : 7^7 ≤ 6^7*(p-1) := by omega
  have hm := Nat.mul_le_mul_right ((p-1)^7) ha
  have hb : p^7 ≤ (p-1)^8 := by
    rw [pow_succ _ 7]
    nlinarith only [h, hm]
  exact hb.trans (Nat.le_mul_of_pos_left _ (smallPrimeCorrection_bounds p).1)

theorem totient_seven_eighth_local (n : ℕ) :
    n^7 ≤ smallPrimeCorrection n*n.totient^8 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => norm_num [smallPrimeCorrection]
  | prime_pow p k hp hk =>
    rw [smallPrimeCorrection_pow hk, Nat.totient_prime_pow hp hk]
    have he : p^k = p^(k-1)*p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he, mul_pow]
    have ha : p^(k-1) ≥ 1 := Nat.one_le_pow _ _ hp.pos
    have hpow : (p^(k-1))^7 ≤ (p^(k-1))^8 :=
      Nat.pow_le_pow_right ha (by omega)
    calc
      _ ≤ (p^(k-1))^8*(smallPrimeCorrection p*(p-1)^8) :=
        Nat.mul_le_mul hpow (prime_seven_eighth hp)
      _ = _ := by ring
  | coprime a b _ _ hab ha hb =>
    rw [smallPrimeCorrection_mul hab, Nat.totient_mul hab, mul_pow, mul_pow]
    exact (Nat.mul_le_mul ha hb).trans_eq (by ring)

theorem totient_seven_eighth (n : ℕ) :
    n^7 ≤ 2401*n.totient^8 := by
  apply (totient_seven_eighth_local n).trans
  exact Nat.mul_le_mul_right _ ((smallPrimeCorrection_bounds n).2.trans (by norm_num))

theorem totient_large_sqrt_ratio {r : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hr : a^4 ≤ (r : ℝ)) :
    a*(r : ℝ)*Real.sqrt r ≤ 7*(r.totient : ℝ)^2 := by
  have hs : (Real.sqrt (r : ℝ))^2 = (r : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have ht : (r : ℝ)^7 ≤ 2401*(r.totient : ℝ)^8 := by
    exact_mod_cast totient_seven_eighth r
  have hmul := mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ (r : ℝ)^6)
  have hpow : (a*(r : ℝ)*Real.sqrt r)^4 ≤ (7*(r.totient : ℝ)^2)^4 := by
    calc
      _ = a^4*(r : ℝ)^6 := by
        calc
          _ = a^4*(r : ℝ)^4*((Real.sqrt r)^2)^2 := by ring
          _ = _ := by rw [hs]; ring
      _ ≤ (r : ℝ)^7 := by nlinarith only [hmul]
      _ ≤ _ := by nlinarith only [ht]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 4 ≠ 0)).mp hpow

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget
