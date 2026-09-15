import LiuWang.Proof.EffectiveLValue.EvenHelpers.IntegralQuotient.IntegralProduct
import LiuWang.Proof.EffectiveLValue.PellLowerBound

/-!
# The full even primitive real-character lower bound

The integral Pell coefficients belong to the original cyclotomic product.
Its logarithm is the already established actual L-value formula.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

variable {r : ℕ} [NeZero r]

theorem evenCharacter_pi_lt_log_largeProduct (χ : Interfaces.Character r)
    (hr : 987 ≤ r) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1) (heven : χ.Even) :
    Real.pi < Real.log (evenCharacterLargeProduct χ) := by
  obtain ⟨v, u, hv, hu, hpell, hV⟩ :=
    evenCharacterLargeProduct_pell_int χ hprimitive hχ heven (by omega)
  rw [hV]
  exact pi_lt_log_pellUnit (by exact_mod_cast hr) hv hu hpell

theorem evenCharacter_LFunction_one_lower (χ : Interfaces.Character r)
    (hr : 987 ≤ r) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1) (heven : χ.Even) :
    Real.pi / Real.sqrt (r : ℝ) ≤ (χ.LFunction 1).re := by
  have hs : 0 < Real.sqrt (r : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos r)
  apply (div_le_iff₀ hs).mpr
  have h := evenCharacter_pi_lt_log_largeProduct χ hr hprimitive hχ heven
  rw [evenCharacterLargeProduct_log χ hprimitive hχ heven (by omega)] at h
  simpa only [mul_comm] using h.le

theorem even_real_primitive_LFunction_one_lower (χ : Interfaces.Character r)
    (hr : 987 ≤ r) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod r, (χ a).im = 0) (heven : χ.Even) :
    Real.pi / Real.sqrt (r : ℝ) ≤ (χ.LFunction 1).re :=
  evenCharacter_LFunction_one_lower χ hr hprimitive
    ((character_sq_eq_one_iff_real χ).mpr hreal) heven

end LiuWang.Proof.EffectiveLValue
