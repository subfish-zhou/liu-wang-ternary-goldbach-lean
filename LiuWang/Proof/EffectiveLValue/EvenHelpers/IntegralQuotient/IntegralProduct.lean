import LiuWang.Proof.EffectiveLValue.EvenHelpers.IntegralQuotient.Denominator
import LiuWang.Proof.EffectiveLValue.EvenHelpers.IntegralQuotient.CoprimeParity

/-!
# Removing the actual rational Pell denominator

A denominator of two forces the nonfundamental shape `r = 4m`, `m = 1 mod 4`.
The parity of the original primitive character rules out precisely this case.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

theorem pell_rat_den_two_forces_four_mul_one_mod_four {r : ℕ} {v : ℤ} {q : ℚ}
    (hpell : (v : ℝ) ^ 2 - r * (q : ℝ) ^ 2 = 4)
    (hden : q.den = 2) (h16 : ¬ 16 ∣ r) :
    ∃ m : ℕ, r = 4 * m ∧ m % 4 = 1 := by
  have : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  have hfour : 4 ∣ r := by simpa [hden] using pell_rat_den_sq_dvd hpell
  obtain ⟨m, hrm⟩ := hfour
  have hq : (q : ℝ) = (q.num : ℝ) / 2 := by rw [Rat.cast_def, hden]; norm_num
  have he : (v : ℝ) ^ 2 - m * (q.num : ℝ) ^ 2 = 4 := by
    rw [hq, hrm, Nat.cast_mul, Nat.cast_ofNat] at hpell
    nlinarith [hpell]
  have hei : v ^ 2 - (m : ℤ) * q.num ^ 2 = 4 := by exact_mod_cast he
  have hodd : Odd q.num := by
    apply Int.natAbs_odd.mp
    apply Nat.coprime_two_right.mp
    simpa [hden] using q.reduced
  have hsq : (q.num : ZMod 4) ^ 2 = 1 := by
    obtain ⟨t, ht⟩ := hodd
    rw [ht]
    push_cast
    calc
      (2 * (t : ZMod 4) + 1) ^ 2 = 1 + 4 * (t ^ 2 + t) := by ring
      _ = 1 := by rw [show (4 : ZMod 4) = 0 by decide, zero_mul, add_zero]
  have hmod : (v : ZMod 4) ^ 2 = (m : ZMod 4) := by
    have h := congrArg (fun z : ℤ ↦ (z : ZMod 4)) hei
    push_cast at h
    rw [hsq, mul_one] at h
    exact sub_eq_zero.mp h
  have hsquares : ∀ z : ZMod 4, z ^ 2 = 0 ∨ z ^ 2 = 1 := by decide
  rcases hsquares v with hv | hv
  · have hm4 : 4 ∣ m := (ZMod.natCast_eq_zero_iff m 4).mp (hmod.symm.trans hv)
    exfalso
    apply h16
    obtain ⟨k, hk⟩ := hm4
    exact ⟨k, by rw [hrm, hk]; ring⟩
  · refine ⟨m, hrm, ?_⟩
    have hm1 : (m : ZMod 4) = 1 := hmod.symm.trans hv
    simpa only [ZMod.val_natCast, ZMod.val_one] using congrArg ZMod.val hm1

theorem primitive_even_quadratic_pell_rat_den_eq_one {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1)
    (heven : χ.Even) {v : ℤ} {q : ℚ}
    (hpell : (v : ℝ) ^ 2 - r * (q : ℝ) ^ 2 = 4) : q.den = 1 := by
  have hd := primitive_quadratic_pell_rat_den_dvd_two χ hprimitive hχ hpell
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hd | hd
  · exact hd
  · obtain ⟨m, hrm, hm⟩ := pell_rat_den_two_forces_four_mul_one_mod_four hpell hd
      (primitive_quadratic_not_sixteen_dvd χ hprimitive hχ)
    have : NeZero m := ⟨by intro hz; simp [hz] at hm⟩
    subst r
    exact False.elim
      (primitive_even_quadratic_not_four_mul_one_mod_four χ hprimitive hχ heven hm)

theorem evenCharacterLargeProduct_pell_int {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1)
    (heven : χ.Even) (hr : 1 < r) :
    ∃ (v u : ℤ), 0 < v ∧ 0 < u ∧
      (v : ℝ) ^ 2 - r * (u : ℝ) ^ 2 = 4 ∧
      evenCharacterLargeProduct χ = ((v : ℝ) + (u : ℝ) * Real.sqrt (r : ℝ)) / 2 := by
  obtain ⟨v, q, hv, hq, hpell, hV⟩ :=
    evenCharacterLargeProduct_pell_rat χ hprimitive hχ heven hr
  have hd := primitive_even_quadratic_pell_rat_den_eq_one χ hprimitive hχ heven hpell
  have hqi : (q.num : ℚ) = q := Rat.coe_int_num_of_den_eq_one hd
  have hqr : (q.num : ℝ) = (q : ℝ) := by exact_mod_cast hqi
  refine ⟨v, q.num, hv, ?_, ?_, ?_⟩
  · rw [← hqi] at hq
    exact_mod_cast hq
  · simpa only [hqr] using hpell
  · simpa only [hqr] using hV

theorem evenCharacter_gauss_quotient_isIntegral {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1)
    (heven : χ.Even) (hr : 1 < r) :
    IsIntegral ℤ ((characterCyclotomicProduct χ - (characterCyclotomicProduct χ)⁻¹) /
      characterGaussSum χ) := by
  obtain ⟨v, q, _, hq, hpell⟩ :=
    evenCharacter_product_pell_rat χ hprimitive hχ heven hr
  have hd := primitive_even_quadratic_pell_rat_den_eq_one χ hprimitive hχ heven hpell
  have hqi : (q.num : ℚ) = q := Rat.coe_int_num_of_den_eq_one hd
  have hi : IsIntegral ℤ (q : ℂ) := by
    rw [← hqi]
    exact isIntegral_algebraMap
  have hU := evenCharacter_product_coe_re χ hprimitive hχ heven hr
  have hT : ((characterGaussSum χ).re : ℂ) = characterGaussSum χ := by
    apply Complex.ext
    · rfl
    · exact (even_characterGaussSum_im χ hχ heven).symm
  have he : characterCyclotomicProduct χ - (characterCyclotomicProduct χ)⁻¹ =
      (q : ℂ) * characterGaussSum χ := by
    rw [← hU, ← hT, ← Complex.ofReal_inv, ← Complex.ofReal_sub]
    exact_mod_cast hq
  rw [he]
  by_cases hz : characterGaussSum χ = 0
  · simp only [hz, mul_zero, div_zero]
    exact isIntegral_zero
  · simpa only [mul_div_cancel_right₀ _ hz] using hi

end LiuWang.Proof.EffectiveLValue
