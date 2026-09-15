import LiuWang.Proof.Campaign20260915.SmallConductors.Consumers
import LiuWang.Proof.Campaign20260915.SmallConductors.Level84

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.SmallConductorExpansion
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.Campaign20260915.SmallConductors

theorem primitive_le_eightyfour_original_region {q : ℕ} [NeZero q]
    (hq : q ≤ 84) (chi : DirichletCharacter ℂ q) (hp : chi.IsPrimitive)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ}
    (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  by_cases h83 : q ≤ 83
  · exact primitive_le_eightythree_original_region h83 chi hp hc hsq hx hqx hb
  have h84 : q = 84 := by omega
  subst q
  exact quadratic_84_original_region chi hc hsq hqx hb

theorem original_source_unpaid84 (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hz : datumL d (beta : ℂ) = 0) :
    85 ≤ d.modulus ∧ d.modulus ≠ 163 ∧ d.modulus % 4 ≠ 2 ∧
      ¬16 ∣ d.modulus ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ^ 2 ∣ d.modulus := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  refine ⟨?_, (original_source_unpaid83 d hx hdx hb hz).2⟩
  by_contra h
  exact primitive_le_eightyfour_original_region (by omega) d.character
    d.isPrimitive d.ne_one d.square_eq_one hx hdx hb hz

theorem actual_exceptional_conductor_restrictions84 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    85 ≤ chi.conductor ∧ chi.conductor ≠ 163 ∧ chi.conductor % 4 ≠ 2 ∧
      ¬16 ∣ chi.conductor ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ^ 2 ∣ chi.conductor := by
  classical
  refine ⟨?_, (actual_exceptional_conductor_restrictions hN hq hr).2⟩
  have hN' := exp_2000_le_of_exp_3100_le hN
  obtain ⟨d, hd, hdc, _, hdz, _⟩ := exceptionalValues_same_source hN' hq hr
  have hi := (exceptionalValues_quadratic_simple hN' hq hr).2.2.1
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hreg := (Finset.mem_filter.mp hr).2
  have hb := r24_re_in_original_real_region (sourceP_ge_ten hN') hreg.1
  have hbound := (original_source_unpaid84 d (sourceP_ge_ten hN') hd hb
    (by simpa only [he] using hdz)).1
  simpa only [hdc] using hbound

#print axioms primitive_le_eightyfour_original_region
#print axioms actual_exceptional_conductor_restrictions84

end LiuWang.Proof.Campaign20260915.SmallConductors
