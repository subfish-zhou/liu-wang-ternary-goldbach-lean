import LiuWang.Proof.Campaign20260915.SmallConductors.Through84
import LiuWang.Proof.Campaign20260915.SmallConductors.Explicit.Batch85_100

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.SmallConductorExpansion
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.EffectiveLValue

namespace LiuWang.Proof.Campaign20260915.SmallConductors

theorem primitive_le_onehundred_original_region {q : ℕ} [NeZero q]
    (hq : q ≤ 100) (chi : DirichletCharacter ℂ q) (hp : chi.IsPrimitive)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ}
    (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  by_cases h84 : q ≤ 84
  · exact primitive_le_eightyfour_original_region h84 chi hp hc hsq hx hqx hb
  have hmod := primitive_mod_four_ne_two chi hp
  have h16 := primitive_quadratic_not_sixteen_dvd chi hp hsq
  have h9 := primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
    (p := 3) (by decide) (by decide)
  have h25 := primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
    (p := 5) (by decide) (by decide)
  norm_num only [show (3 : ℕ) ^ 2 = 9 by decide,
    show (5 : ℕ) ^ 2 = 25 by decide] at h9 h25
  simp only [Nat.dvd_iff_mod_eq_zero] at h16 h9 h25
  have he : q = 85 ∨ q = 87 ∨ q = 88 ∨ q = 89 ∨ q = 91 ∨ q = 92 ∨
      q = 93 ∨ q = 95 ∨ q = 97 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Explicit.level85 chi hc hsq hqx hb
  · exact Explicit.level87 chi hc hsq hqx hb
  · exact Explicit.level88 chi hc hsq hqx hb
  · exact Explicit.level89 chi hc hsq hqx hb
  · exact Explicit.level91 chi hc hsq hqx hb
  · exact Explicit.level92 chi hc hsq hqx hb
  · exact Explicit.level93 chi hc hsq hqx hb
  · exact Explicit.level95 chi hc hsq hqx hb
  · exact Explicit.level97 chi hc hsq hqx hb

theorem original_source_unpaid100 (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hz : datumL d (beta : ℂ) = 0) :
    101 ≤ d.modulus ∧ d.modulus ≠ 163 ∧ d.modulus % 4 ≠ 2 ∧
      ¬16 ∣ d.modulus ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ^ 2 ∣ d.modulus := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  refine ⟨?_, (original_source_unpaid84 d hx hdx hb hz).2⟩
  by_contra h
  exact primitive_le_onehundred_original_region (by omega) d.character
    d.isPrimitive d.ne_one d.square_eq_one hx hdx hb hz

theorem actual_exceptional_conductor_restrictions100 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    101 ≤ chi.conductor ∧ chi.conductor ≠ 163 ∧ chi.conductor % 4 ≠ 2 ∧
      ¬16 ∣ chi.conductor ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ^ 2 ∣ chi.conductor := by
  classical
  refine ⟨?_, (actual_exceptional_conductor_restrictions84 hN hq hr).2⟩
  have hN' := exp_2000_le_of_exp_3100_le hN
  obtain ⟨d, hd, hdc, _, hdz, _⟩ := exceptionalValues_same_source hN' hq hr
  have hi := (exceptionalValues_quadratic_simple hN' hq hr).2.2.1
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hreg := (Finset.mem_filter.mp hr).2
  have hb := r24_re_in_original_real_region (sourceP_ge_ten hN') hreg.1
  have hbound := (original_source_unpaid100 d (sourceP_ge_ten hN') hd hb
    (by simpa only [he] using hdz)).1
  simpa only [hdc] using hbound

#print axioms primitive_le_onehundred_original_region
#print axioms actual_exceptional_conductor_restrictions100

end LiuWang.Proof.Campaign20260915.SmallConductors
