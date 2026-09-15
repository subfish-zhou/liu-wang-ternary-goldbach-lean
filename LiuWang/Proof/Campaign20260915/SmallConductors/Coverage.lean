import LiuWang.Proof.Campaign20260915.SmallConductors.TwiceOdd
import LiuWang.Proof.Campaign20260915.SmallConductors.Prime83
import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Batch65_80
import LiuWang.Proof.EffectiveLValue.EvenHelpers.IntegralQuotient.Conductor

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.SmallConductorExpansion.Continuation
open LiuWang.Proof.EffectiveLValue

namespace LiuWang.Proof.Campaign20260915.SmallConductors

theorem primitive_le_eightythree_original_region {q : ℕ} [NeZero q]
    (hq : q ≤ 83) (chi : DirichletCharacter ℂ q) (hp : chi.IsPrimitive)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ}
    (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  by_cases h64 : q ≤ 64
  · exact quadratic_level_le_sixtyfour_original_region h64 chi hc hsq hx hqx hb
  by_cases h80 : q ≤ 80
  · exact VerifiedScan.batch65_80 (by omega) h80 chi hc hsq hqx hb
  have he : q = 81 ∨ q = 82 ∨ q = 83 := by omega
  rcases he with rfl | rfl | rfl
  · exact (primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
      (p := 3) (by decide) (by decide) (by decide)).elim
  · exact (primitive_mod_four_ne_two chi hp (by decide)).elim
  · exact quadratic_83_original_region chi hc hsq hqx hb

theorem primitive_original_real_zero_unpaid83 {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hp : chi.IsPrimitive)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ}
    (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hz : chi.LFunction (beta : ℂ) = 0) :
    84 ≤ q ∧ q ≠ 163 ∧ q % 4 ≠ 2 ∧ ¬16 ∣ q ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ^ 2 ∣ q := by
  refine ⟨?_, ?_, primitive_mod_four_ne_two chi hp,
    primitive_quadratic_not_sixteen_dvd chi hp hsq, ?_⟩
  · by_contra h
    exact primitive_le_eightythree_original_region (by omega) chi hp hc hsq hx hqx hb hz
  · intro he
    subst q
    exact quadratic_163_original_region chi hc hsq hqx hb hz
  · intro p hprime htwo
    exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq hprime htwo

theorem original_source_unpaid83 (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hz : datumL d (beta : ℂ) = 0) :
    84 ≤ d.modulus ∧ d.modulus ≠ 163 ∧ d.modulus % 4 ≠ 2 ∧
      ¬16 ∣ d.modulus ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ^ 2 ∣ d.modulus := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  exact primitive_original_real_zero_unpaid83 d.character d.isPrimitive d.ne_one
    d.square_eq_one hx hdx hb hz

#print axioms primitive_le_eightythree_original_region
#print axioms original_source_unpaid83

end LiuWang.Proof.Campaign20260915.SmallConductors
