import LiuWang.Proof.EffectiveLValue.EvenHelpers.IntegralQuotient.Conductor
import LiuWang.Proof.EffectiveLValue.EvenHelpers.ProductPell

/-!
# Denominators in the actual character's Pell relation

Primitivity removes all odd denominator primes and bounds the remaining
denominator by two. The possible denominator two is kept explicit.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

theorem pell_rat_den_sq_dvd {r : ℕ} {v : ℤ} {q : ℚ}
    (hpell : (v : ℝ) ^ 2 - r * (q : ℝ) ^ 2 = 4) : q.den ^ 2 ∣ r := by
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hq : (q : ℝ) * q.den = q.num := by rw [Rat.cast_def]; exact div_mul_cancel₀ _ hd
  have he : (r : ℝ) * (q.num : ℝ) ^ 2 =
      ((v : ℝ) ^ 2 - 4) * (q.den : ℝ) ^ 2 := by
    rw [← hq]
    nlinarith [congrArg (fun x : ℝ ↦ x * (q.den : ℝ) ^ 2) hpell]
  have hei : (r : ℤ) * q.num ^ 2 = (v ^ 2 - 4) * (q.den : ℤ) ^ 2 := by
    exact_mod_cast he
  have hdiv : (q.den : ℤ) ^ 2 ∣ (r : ℤ) * q.num ^ 2 := by
    rw [hei]
    exact dvd_mul_left _ _
  have hnat : q.den ^ 2 ∣ r * q.num.natAbs ^ 2 := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using
      Int.natAbs_dvd_natAbs.mpr hdiv
  exact (q.reduced.symm.pow 2 2).dvd_of_dvd_mul_right hnat

theorem primitive_quadratic_pell_rat_den_dvd_two {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1)
    {v : ℤ} {q : ℚ} (hpell : (v : ℝ) ^ 2 - r * (q : ℝ) ^ 2 = 4) :
    q.den ∣ 2 := by
  have hd := pell_rat_den_sq_dvd hpell
  have hprime : ∀ {p : ℕ}, p.Prime → p ∣ q.den → p = 2 := by
    intro p hp hpd
    by_contra hp2
    exact primitive_quadratic_not_odd_prime_sq_dvd χ hprimitive hχ hp hp2
      ((pow_dvd_pow_of_dvd hpd 2).trans hd)
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz hprime
  have hlen : q.den.primeFactorsList.length ≤ 1 := by
    by_contra h
    have hfour : 4 ∣ q.den := by
      rw [hpow]
      exact pow_dvd_pow 2 (by omega : 2 ≤ q.den.primeFactorsList.length)
    exact primitive_quadratic_not_sixteen_dvd χ hprimitive hχ
      ((pow_dvd_pow_of_dvd hfour 2).trans hd)
  rw [hpow]
  exact pow_dvd_pow 2 hlen

theorem evenCharacterLargeProduct_pell_half_integral {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1)
    (heven : χ.Even) (hr : 1 < r) :
    ∃ (v : ℤ) (q : ℚ), 0 < v ∧ 0 < q ∧ q.den ∣ 2 ∧
      (v : ℝ) ^ 2 - r * (q : ℝ) ^ 2 = 4 ∧
      evenCharacterLargeProduct χ = ((v : ℝ) + (q : ℝ) * Real.sqrt (r : ℝ)) / 2 := by
  obtain ⟨v, q, hv, hq, hpell, hV⟩ :=
    evenCharacterLargeProduct_pell_rat χ hprimitive hχ heven hr
  exact ⟨v, q, hv, hq, primitive_quadratic_pell_rat_den_dvd_two χ hprimitive hχ hpell,
    hpell, hV⟩

end LiuWang.Proof.EffectiveLValue
