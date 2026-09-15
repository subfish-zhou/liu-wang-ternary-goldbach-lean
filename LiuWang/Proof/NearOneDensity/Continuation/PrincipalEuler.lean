import LiuWang.Proof.NearOneDensity.Continuation.MixedPhase

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity.Continuation

def smallPrimeAllowance (p : ℕ) : ℝ :=
  (if p = 2 then 53 / 100 else 0) + (if p = 3 then 38 / 100 else 0) +
    (if p = 5 then 22 / 100 else 0) + (if p = 7 then 12 / 100 else 0)

theorem primeCost_tenth {p : ℕ} (hp : p.Prime) {σ : ℝ}
    (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) :
    primeCost p σ ≤ (1 / 10) * Real.log p + smallPrimeAllowance p := by
  have hb := primeCost_le_rational_power hp hσ hσ₁
  have hk := mul_le_mul_of_nonneg_right stechkinK_ge_447 (Real.log_natCast_nonneg p)
  by_cases h2 : p = 2
  · subst p
    norm_num [smallPrimeAllowance] at hb ⊢
    have hh := Real.log_two_lt_d9
    nlinarith
  by_cases h3 : p = 3
  · subst p
    norm_num [smallPrimeAllowance] at hb ⊢
    have hh := Real.log_three_lt_d9
    nlinarith
  by_cases h5 : p = 5
  · subst p
    norm_num [smallPrimeAllowance] at hb ⊢
    have hh := Real.log_five_lt_d9
    nlinarith
  by_cases h7 : p = 7
  · subst p
    have hlog : Real.log 7 ≤ 2 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7 / 8)
      rw [Real.log_div (by norm_num) (by norm_num),
        show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at hh
      norm_num at hh
      linarith [Real.log_two_lt_d9]
    norm_num [smallPrimeAllowance] at hb ⊢
    nlinarith
  have h11 : 11 ≤ p := by
    by_contra hh
    have hp0 : p < 11 := by omega
    interval_cases p <;> norm_num at *
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast h11
  have hrec : 1 / ((p : ℝ) - 1) ≤ (1 / 10 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hneg : 0 ≤ stechkinK / ((p : ℝ) ^ 2 - 1) :=
    div_nonneg stechkinK_mem.1 (by nlinarith)
  have hh := mul_le_mul_of_nonneg_left (show
    1 / ((p : ℝ) - 1) - stechkinK / ((p : ℝ) ^ 2 - 1) ≤ 1 / 10 by linarith)
    (Real.log_natCast_nonneg p)
  simp only [smallPrimeAllowance, if_neg h2, if_neg h3, if_neg h5, if_neg h7, add_zero]
  nlinarith

theorem sum_smallPrimeAllowance_le (s : Finset ℕ) :
    (∑ p ∈ s, smallPrimeAllowance p) ≤ 5 / 4 := by
  have hf (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
      (∑ p ∈ s, if p = n then c else 0) ≤ c := by
    simp only [Finset.sum_ite_eq']
    split <;> simp_all
  simp only [smallPrimeAllowance, Finset.sum_add_distrib]
  linarith [hf 2 (53 / 100) (by norm_num), hf 3 (38 / 100) (by norm_num),
    hf 5 (22 / 100) (by norm_num), hf 7 (12 / 100) (by norm_num)]

theorem prime_support_log_le (q : ℕ) [NeZero q] :
    (∑ p ∈ q.primeFactors, Real.log p) ≤ Real.log q := by
  have hh := disjoint_prime_support_log (NeZero.pos q) (by norm_num : 0 < 1)
    (one_dvd q) q.primeFactors (fun _ h => h) (fun _ _ => Nat.coprime_one_right _)
  simpa using hh

theorem principalPrimeCost_tenth (q : ℕ) [NeZero q] {σ : ℝ}
    (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) :
    principalPrimeCost q σ ≤ (1 / 10) * Real.log q + 5 / 4 := by
  have hh := Finset.sum_le_sum (s := q.primeFactors)
    (fun p hp => primeCost_tenth (Nat.prime_of_mem_primeFactors hp) hσ hσ₁)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have hl := mul_le_mul_of_nonneg_left (prime_support_log_le q) (by norm_num : (0 : ℝ) ≤ 1 / 10)
  exact (by
    change (∑ p ∈ q.primeFactors, primeCost p σ) ≤ _
    linarith [sum_smallPrimeAllowance_le q.primeFactors])

theorem principalPrimeCost_kappa (q : ℕ) [NeZero q] {σ : ℝ}
    (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) :
    principalPrimeCost q σ ≤ stechkinConductorCoeff * Real.log q + 941 / 1600 := by
  have hk : 0 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_mem.2]
  have hh := finite_primeCost_budget q.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) hσ hσ₁
  have hl := mul_le_mul_of_nonneg_left (prime_support_log_le q) hk
  change (∑ p ∈ q.primeFactors, primeCost p σ) ≤ _
  linarith

end LiuWang.Proof.NearOneDensity.Continuation
