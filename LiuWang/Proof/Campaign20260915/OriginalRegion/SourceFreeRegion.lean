import LiuWang.Proof.Campaign20260915.OriginalRegion.SelectedMovingCost
import LiuWang.Proof.Campaign20260915.OriginalRegion.SimultaneousSelection
import LiuWang.Proof.Campaign20260915.OriginalRegion.PrincipalRegion
import LiuWang.Proof.Campaign20260915.OriginalRegion.SmallOrderClassification

/-! All characters and all closed heights at the stated paper-scale lower bound. -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem primitive_source_free_original_closed {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 8000000000 ≤ x) {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1)
    (hp : chi.IsPrimitive) {rho : ℂ} (hscale : (q : ℝ) * max 1 |rho.im| ≤ x)
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (hbranch : chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hlog := source_log_twenty_two hx
  have hL : 0 < Real.log x := by linarith
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / 10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra hh
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt hh) hz
  obtain ⟨hA, hAm, _⟩ := lectureShift_properties
  let u := lectureShift / Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 / 50 := by
    apply (div_le_iff₀ hL).mpr
    linarith
  have hgap : (1 - rho.re) * Real.log x ≤ 1 / 9.645908801 := by
    have hh := (le_div_iff₀ (show 0 < 9.645908801 * Real.log x by positivity)).mp
      (show 1 - rho.re ≤ 1 / (9.645908801 * Real.log x) by linarith)
    nlinarith only [hh]
  have hgap1 : 1 - rho.re ≤ (1 + u) - 1 := by
    have hh : 1 - rho.re ≤ u :=
      (le_div_iff₀ hL).mpr (hgap.trans originalGap_le_lectureShift)
    linarith
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have htpos : 0 < max 1 |rho.im| := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlogs : Real.log q + Real.log (max 1 |rho.im|) ≤ Real.log x := by
    rw [← Real.log_mul hqpos.ne' htpos.ne']
    exact Real.log_le_log (mul_pos hqpos htpos) hscale
  have he := lecture_signed_moving_envelope hc hp (sigma := 1 + u)
    (by linarith) (by linarith) rho.im
  have hpoles := all_nonprincipal_lecture_poles_paid chi hc (by linarith) hb hz hbranch
    (sigma := 1 + u) (by linarith) (by linarith) hgap1
  have hk := selected_pair_dominates (sigma := 1 + u) (by linarith)
    (rho := rho) ⟨by linarith, hb⟩
  change 1 / (1 + u - rho.re) ≤ reflectedKernel (1 + u) rho.im rho at hk
  have hupper := mul_le_mul_of_nonneg_left hlogs
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 36.506331844352) conductorCoeff_bounds.1)
  have heuler := principalPrimeCost_nonneg q (sigma := 1 + u) (by linarith)
  have hpaid : 19.073344004352 / (1 + u - rho.re) ≤
      11.1859355312082048 / u + 36.506331844352 * stechkinConductorCoeff * Real.log x := by
    norm_num only [add_sub_cancel_left] at he
    simp only [div_eq_mul_inv] at *
    nlinarith
  exact lecture_scaled_budget_contradiction hL hb hgap hpaid

theorem ordinary_source_free_original_closed {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 8000000000 ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hscale : (q : ℝ) * max 1 |rho.im| ≤ x)
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (hbranch : chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hL : 0 < Real.log x := by linarith [source_log_twenty_two hx]
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / 10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [source_log_twenty_two hx]
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  exact primitive_source_free_original_closed hx
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive
    ((mul_le_mul_of_nonneg_right hcq (by positivity)).trans hscale) hr
    (hbranch.imp
      (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_ne_one_of_pow_ne_one chi) id)
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc (by linarith) hz)

theorem source_free_original_classification_closed {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re) (hr1 : rho.re < 1)
    (ht : |rho.im| ≤ x / q) (hz : chi.LFunction rho = 0) :
    chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0 ∧ analyticOrderNatAt chi.LFunction rho = 1 := by
  have hx10 : 10 ≤ x := by linarith
  have hc : chi ≠ 1 := by
    intro he
    subst chi
    exact principal_original_no_zero_closed hx10 hr ht (by intro hh; simp [hh] at hr1) hz
  have hscale : (q : ℝ) * max 1 |rho.im| ≤ x := by
    by_cases hh : |rho.im| ≤ 1
    · simpa only [max_eq_left hh, mul_one] using hq
    · rw [max_eq_right (le_of_not_ge hh)]
      simpa only [mul_comm] using
        (le_div_iff₀ (show 0 < (q : ℝ) by exact_mod_cast NeZero.pos q)).mp ht
  have hb : chi ^ 2 = 1 ∧ rho.im = 0 := by
    by_contra hh
    push Not at hh
    by_cases h2 : chi ^ 2 = 1
    · exact ordinary_source_free_original_closed hx chi hc hscale hr (Or.inr (hh h2)) hz
    · exact ordinary_source_free_original_closed hx chi hc hscale hr (Or.inl h2) hz
  have hL : 0 < Real.log x := by linarith [source_log_twenty_two hx]
  have hw : 1 / (9.645908801 * Real.log x) < 1 / (8 * Real.log x) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hg : 1 - rho.re < 1 / (8 * Real.log x) := by linarith
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hb.2]
  have hm := ordinary_real_zero_simple_eight hx10 hq chi hc hg (by simpa only [he] using hz)
  rw [he] at hm
  exact ⟨hc, hb.1, hb.2, hm⟩

theorem source_free_original_classification {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re) (hr1 : rho.re < 1)
    (ht : |rho.im| ≤ x / q) (hz : chi.LFunction rho = 0) :
    chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0 ∧ analyticOrderNatAt chi.LFunction rho = 1 :=
  source_free_original_classification_closed hx hq chi hr.le hr1 ht hz

end LiuWang.Proof.Campaign20260915.OriginalRegion
