import LiuWang.Proof.EffectiveLValue.AllParityLowerBound

/-!
# Original-domain consumers at the requested cutoff

No integrality, conductor shape, class number, or unit is an input.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue.IntegralConsumer

variable {r : ℕ} [NeZero r]

theorem actual_even_quotient_integral (χ : Interfaces.Character r) (hr : 987 ≤ r)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0) (heven : χ.Even) :
    IsIntegral ℤ ((characterCyclotomicProduct χ - (characterCyclotomicProduct χ)⁻¹) /
      characterGaussSum χ) :=
  evenCharacter_gauss_quotient_isIntegral χ hprimitive
    ((character_sq_eq_one_iff_real χ).mpr hreal) heven (by omega)

theorem actual_even_pell_integer (χ : Interfaces.Character r) (hr : 987 ≤ r)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0) (heven : χ.Even) :
    ∃ (v u : ℤ), 0 < v ∧ 0 < u ∧
      (v : ℝ) ^ 2 - r * (u : ℝ) ^ 2 = 4 ∧
      evenCharacterLargeProduct χ = ((v : ℝ) + (u : ℝ) * Real.sqrt (r : ℝ)) / 2 :=
  evenCharacterLargeProduct_pell_int χ hprimitive
    ((character_sq_eq_one_iff_real χ).mpr hreal) heven (by omega)

theorem actual_even_branch (χ : Interfaces.Character r) (hr : 987 ≤ r)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0) (heven : χ.Even) :
    Real.pi / Real.sqrt (r : ℝ) ≤ (χ.LFunction 1).re :=
  even_real_primitive_LFunction_one_lower χ hr hprimitive hreal heven

theorem actual_all_parity (χ : Interfaces.Character r) (hr : 987 ≤ r)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0) :
    Real.pi / Real.sqrt (r : ℝ) ≤ (χ.LFunction 1).re :=
  real_primitive_LFunction_one_lower χ hr hprimitive hreal

theorem cutoff_987 (χ : Interfaces.Character 987) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod 987, (χ a).im = 0) :
    Real.pi / Real.sqrt (987 : ℝ) ≤ (χ.LFunction 1).re :=
  actual_all_parity χ (by norm_num) hprimitive hreal

end LiuWang.Proof.EffectiveLValue.IntegralConsumer
