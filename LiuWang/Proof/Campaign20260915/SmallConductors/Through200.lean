import LiuWang.Proof.Campaign20260915.SmallConductors.Through150
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Batch151_200
import LiuWang.Proof.WeightedLowZeros.Continuation.PaperSource

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.SmallConductorExpansion
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors

theorem primitive_le_200_original_region {q : ℕ} [NeZero q]
    (hq : q ≤ 200) (chi : DirichletCharacter ℂ q) (hp : chi.IsPrimitive)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ}
    (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  by_cases hprev : q ≤ 150
  · exact primitive_le_onehundredfifty_original_region hprev chi hp hc hsq hx hqx hb
  · exact Fast.range_151_200 (by omega) hq chi hp hc hsq hqx hb

theorem original_source_conductor_ge_201 (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hz : datumL d (beta : ℂ) = 0) : 201 ≤ d.modulus := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  by_contra h
  exact primitive_le_200_original_region (by omega) d.character
    d.isPrimitive d.ne_one d.square_eq_one hx hdx hb hz

theorem actual_exceptional_conductor_ge_201 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    201 ≤ chi.conductor := by
  classical
  have hN' := exp_2000_le_of_exp_3100_le hN
  obtain ⟨d, hd, hdc, _, hdz, _⟩ := exceptionalValues_same_source hN' hq hr
  have hi := (exceptionalValues_quadratic_simple hN' hq hr).2.2.1
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hreg := (Finset.mem_filter.mp hr).2
  have hb := r24_re_in_original_real_region (sourceP_ge_ten hN') hreg.1
  have hbound := original_source_conductor_ge_201 d
    (sourceP_ge_ten hN') hd hb (by simpa only [he] using hdz)
  simpa only [hdc] using hbound

theorem paper_source_conductor_ge_201 {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    201 ≤ (d.modulus : ℝ) := by
  have he : (e.re : ℂ) = e := by apply Complex.ext <;> simp [hd.2.2.1]
  have h := original_source_conductor_ge_201 d
    (sourceP_ge_ten (exp_2000_le_of_exp_3100_le hN)) hd.1 hd.2.2.2.2.le
    (by simpa only [he] using hd.2.1)
  exact_mod_cast h

#print axioms primitive_le_200_original_region
#print axioms actual_exceptional_conductor_ge_201
#print axioms paper_source_conductor_ge_201

end LiuWang.Proof.Campaign20260915.SmallConductors
