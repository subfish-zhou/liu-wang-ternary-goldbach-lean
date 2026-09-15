import LiuWang.Proof.EffectiveLValue.EvenHelpers.CyclotomicGalois
import LiuWang.Proof.EffectiveLValue.EvenValueFormula

/-!
# The original cyclotomic product's trace and rational Pell coefficient

The trace is an integer, and the anti-invariant part divided by the original
Gauss sum is rational. Integrality of this rational coefficient is **not**
asserted. That is a remaining arithmetic obligation, not a regulator assumption.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open Complex Finset

variable {r : ℕ} [NeZero r]

theorem characterCyclotomicProduct_trace_int (χ : Interfaces.Character r)
    (hreal : χ ^ 2 = 1) (hne : χ ≠ 1) (hr : 1 < r) :
    ∃ v : ℤ, characterCyclotomicProduct χ + (characterCyclotomicProduct χ)⁻¹ = (v : ℂ) := by
  let U := characterCyclotomicProductInField χ
  have hfix : U + U⁻¹ ∈ (⊥ : IntermediateField ℚ (characterCyclotomicAmbient r)) := by
    apply (IsGalois.mem_bot_iff_fixed _).mpr
    intro σ
    rw [map_add, map_inv₀]
    rcases characterCyclotomicProductInField_aut_cases χ hreal σ with h | h
    · change σ U = U at h
      rw [h]
    · change σ U = U⁻¹ at h
      rw [h, inv_inv, add_comm]
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hfix
  have hqc : (q : ℂ) = characterCyclotomicProduct χ + (characterCyclotomicProduct χ)⁻¹ := by
    have h := congrArg (characterCyclotomicAmbient r).val hq
    change (q : ℂ) = (U : ℂ) + (U : ℂ)⁻¹ at h
    simpa only [U, characterCyclotomicProductInField_coe] using h
  have hi : IsIntegral ℤ (q : ℂ) := by
    rw [hqc]
    exact (characterCyclotomicProduct_isIntegral χ hreal hne hr).add
      (characterCyclotomicProduct_inv_isIntegral χ hreal hne hr)
  have hiq : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hi
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp hiq
  refine ⟨v, ?_⟩
  rw [← hqc, ← hv]
  norm_cast

theorem characterCyclotomicProduct_gauss_quotient_rat (χ : Interfaces.Character r)
    (hreal : χ ^ 2 = 1) :
    ∃ q : ℚ, (characterCyclotomicProduct χ - (characterCyclotomicProduct χ)⁻¹) /
      characterGaussSum χ = (q : ℂ) := by
  let U := characterCyclotomicProductInField χ
  let T := characterGaussSumInField χ
  have hfix : (U - U⁻¹) / T ∈ (⊥ : IntermediateField ℚ (characterCyclotomicAmbient r)) := by
    apply (IsGalois.mem_bot_iff_fixed _).mpr
    intro σ
    change σ ((characterCyclotomicProductInField χ - (characterCyclotomicProductInField χ)⁻¹) /
      characterGaussSumInField χ) = _
    rw [map_div₀, map_sub, map_inv₀, characterCyclotomicProductInField_aut χ hreal,
      characterGaussSumInField_aut χ hreal]
    rcases realCharacterSign_unit χ hreal (characterCyclotomicAutIndex σ) with h | h
    · simp [h, U, T]
    · simp only [h, zpow_neg_one, inv_inv, Int.cast_neg, Int.cast_one, neg_one_mul]
      change (U⁻¹ - U) / (-T) = (U - U⁻¹) / T
      rw [show U⁻¹ - U = -(U - U⁻¹) by ring, neg_div_neg_eq]
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hfix
  refine ⟨q, ?_⟩
  have h := congrArg (characterCyclotomicAmbient r).val hq
  change (q : ℂ) = ((U : ℂ) - (U : ℂ)⁻¹) / (T : ℂ) at h
  simpa only [U, T,
    characterCyclotomicProductInField_coe, characterGaussSumInField_coe χ hreal] using h.symm

theorem evenCharacter_product_coe_re (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    ((characterCyclotomicProduct χ).re : ℂ) = characterCyclotomicProduct χ := by
  apply Complex.ext
  · rfl
  · exact (evenCharacter_product_im χ hprimitive hreal heven hr).symm

theorem evenCharacter_product_pell_rat (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    ∃ (v : ℤ) (q : ℚ),
      (characterCyclotomicProduct χ).re + ((characterCyclotomicProduct χ).re)⁻¹ = v ∧
      (characterCyclotomicProduct χ).re - ((characterCyclotomicProduct χ).re)⁻¹ =
        q * (characterGaussSum χ).re ∧
      (v : ℝ) ^ 2 - r * (q : ℝ) ^ 2 = 4 := by
  obtain ⟨v, hv⟩ := characterCyclotomicProduct_trace_int χ hreal
    (primitiveCharacter_ne_one χ hprimitive hr) hr
  obtain ⟨q, hq⟩ := characterCyclotomicProduct_gauss_quotient_rat χ hreal
  have hT : (characterGaussSum χ).re ≠ 0 := by
    have h := even_characterGaussSum_re_sq χ hprimitive hreal heven hr
    intro hz
    rw [hz] at h
    have hr0 : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
    nlinarith
  have hTc : characterGaussSum χ ≠ 0 := by
    intro hz
    exact hT (by rw [hz]; rfl)
  have hq' := (div_eq_iff hTc).mp hq
  have hU := evenCharacter_product_coe_re χ hprimitive hreal heven hr
  have hvr := congrArg Complex.re hv
  have hqr := congrArg Complex.re hq'
  rw [← hU] at hvr hqr
  simp only [← Complex.ofReal_inv, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.intCast_re, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
    zero_mul, sub_zero] at hvr hqr
  refine ⟨v, q, hvr, hqr, ?_⟩
  have hp := evenCharacter_product_pos χ hprimitive hreal heven hr
  have hm := mul_inv_cancel₀ hp.ne'
  have hs := even_characterGaussSum_re_sq χ hprimitive hreal heven hr
  have hqs := congrArg (fun x : ℝ ↦ x ^ 2) hqr
  rw [mul_pow] at hqs
  rw [← hvr, ← hs]
  nlinarith

def evenCharacterLargeProduct (χ : Interfaces.Character r) : ℝ :=
  max (characterCyclotomicProduct χ).re ((characterCyclotomicProduct χ).re)⁻¹

theorem evenCharacterLargeProduct_gt_one (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    1 < evenCharacterLargeProduct χ := by
  have hp := evenCharacter_product_pos χ hprimitive hreal heven hr
  have hn : (characterCyclotomicProduct χ).re ≠ 1 := by
    intro h
    apply evenCharacter_product_ne_one χ hprimitive hreal heven hr
    rw [← evenCharacter_product_coe_re χ hprimitive hreal heven hr, h, Complex.ofReal_one]
  rcases lt_or_gt_of_ne hn with h | h
  · exact (one_lt_inv₀ hp).mpr h |>.trans_le (le_max_right _ _)
  · exact h.trans_le (le_max_left _ _)

theorem evenCharacterLargeProduct_log (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    Real.log (evenCharacterLargeProduct χ) =
      Real.sqrt (r : ℝ) * (χ.LFunction 1).re := by
  rw [← evenCharacter_abs_log_product χ hprimitive hreal heven hr]
  have hp := evenCharacter_product_pos χ hprimitive hreal heven hr
  by_cases h : 1 ≤ (characterCyclotomicProduct χ).re
  · have hi : ((characterCyclotomicProduct χ).re)⁻¹ ≤ (characterCyclotomicProduct χ).re :=
      (inv_le_one_of_one_le₀ h).trans h
    rw [evenCharacterLargeProduct, max_eq_left hi, abs_of_nonneg (Real.log_nonneg h)]
  · have h' : (characterCyclotomicProduct χ).re ≤ 1 := (lt_of_not_ge h).le
    have hi : (characterCyclotomicProduct χ).re ≤ ((characterCyclotomicProduct χ).re)⁻¹ :=
      h'.trans ((one_le_inv₀ hp).mpr h')
    rw [evenCharacterLargeProduct, max_eq_right hi, Real.log_inv,
      abs_of_nonpos (Real.log_nonpos hp.le h')]

theorem evenCharacterLargeProduct_pell_rat (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (heven : χ.Even) (hr : 1 < r) :
    ∃ (v : ℤ) (q : ℚ), 0 < v ∧ 0 < q ∧
      (v : ℝ) ^ 2 - r * (q : ℝ) ^ 2 = 4 ∧
      evenCharacterLargeProduct χ = ((v : ℝ) + (q : ℝ) * Real.sqrt (r : ℝ)) / 2 := by
  obtain ⟨v, q, hv, hq, hpell⟩ := evenCharacter_product_pell_rat χ hprimitive hreal heven hr
  have hp := evenCharacter_product_pos χ hprimitive hreal heven hr
  have hn : (characterCyclotomicProduct χ).re ≠ 1 := by
    intro h
    apply evenCharacter_product_ne_one χ hprimitive hreal heven hr
    rw [← evenCharacter_product_coe_re χ hprimitive hreal heven hr, h, Complex.ofReal_one]
  have hvpos : 0 < v := by
    have h := add_pos hp (inv_pos.mpr hp)
    rw [hv] at h
    exact_mod_cast h
  have hqne : q ≠ 0 := by
    intro h
    rw [h, Rat.cast_zero, zero_mul] at hq
    have hm := mul_inv_cancel₀ hp.ne'
    have he : (characterCyclotomicProduct χ).re = ((characterCyclotomicProduct χ).re)⁻¹ :=
      sub_eq_zero.mp hq
    rw [← he] at hm
    apply hn
    nlinarith
  have hqa := congrArg abs hq
  rw [abs_mul, even_characterGaussSum_abs_re χ hprimitive hreal heven hr,
    ← Rat.cast_abs] at hqa
  refine ⟨v, |q|, hvpos, abs_pos.mpr hqne, ?_, ?_⟩
  · simpa only [Rat.cast_abs, sq_abs] using hpell
  · unfold evenCharacterLargeProduct
    rcases le_total ((characterCyclotomicProduct χ).re)⁻¹ (characterCyclotomicProduct χ).re
      with h | h
    · rw [max_eq_left h]
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hqa
      linarith
    · rw [max_eq_right h]
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hqa
      linarith

end LiuWang.Proof.EffectiveLValue
