import LiuWang.Proof.Campaign20260915.OriginalRegion.LectureScalar
import LiuWang.Proof.Campaign20260915.OriginalRegion.FourthOrderLow

/-! Source-free original-c1 exclusion when the first four powers are nonprincipal. -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem primitive_higher_order_original {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1)
    (hp : chi.IsPrimitive) (h2 : chi ^ 2 ≠ 1) (h3 : chi ^ 3 ≠ 1) (h4 : chi ^ 4 ≠ 1)
    {rho : ℂ} (hscale : (q : ℝ) * max 1 |rho.im| ≤ x)
    (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re) :
    chi.LFunction rho ≠ 0 := by
  intro hz
  have hlog := log_scale_ge_34_15 hx
  have hL : 0 < Real.log x := by linarith
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra hh
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt hh) hz
  obtain ⟨hA, hAm, _⟩ := lectureShift_properties
  let u := lectureShift / Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3 / 20 := by
    apply (div_le_iff₀ hL).mpr
    linarith
  have hdu : (1 - rho.re) * Real.log x < 1 / 9.645908801 := by
    have hh := (lt_div_iff₀ (show 0 < 9.645908801 * Real.log x by positivity)).mp
      (show 1 - rho.re < 1 / (9.645908801 * Real.log x) by linarith)
    nlinarith only [hh]
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have htpos : 0 < max 1 |rho.im| := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlogs : Real.log q + Real.log (max 1 |rho.im|) ≤ Real.log x := by
    rw [← Real.log_mul hqpos.ne' htpos.ne']
    exact Real.log_le_log (mul_pos hqpos htpos) hscale
  have hh := higher_order_lecture_budget hc hp h2 h3 h4 (by linarith) hz
    (sigma := 1 + u) (by linarith) (by linarith)
  have hupper := mul_le_mul_of_nonneg_left hlogs
    (show 0 ≤ 36.506331844352 * stechkinConductorCoeff by
      exact mul_nonneg (by norm_num) conductorCoeff_bounds.1)
  have hpaid : 19.073344004352 / (1 + u - rho.re) ≤
      11.1859355312082048 / u + 36.506331844352 * stechkinConductorCoeff * Real.log x := by
    have hp0 := principalPrimeCost_nonneg q (show 1 < 1 + u by linarith)
    norm_num only [add_sub_cancel_left] at hh
    linarith
  exact lecture_scaled_budget_contradiction hL hb hdu.le hpaid

theorem ordinary_higher_order_original {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (chi : DirichletCharacter ℂ q)
    (h2 : chi ^ 2 ≠ 1) (h3 : chi ^ 3 ≠ 1) (h4 : chi ^ 4 ≠ 1)
    {rho : ℂ} (hscale : (q : ℝ) * max 1 |rho.im| ≤ x)
    (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re) :
    chi.LFunction rho ≠ 0 := by
  intro hz
  have hc : chi ≠ 1 := by intro hh; apply h2; simp [hh]
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [log_scale_ge_34_15 hx]
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  exact primitive_higher_order_original hx
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_ne_one_of_pow_ne_one chi h2)
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_ne_one_of_pow_ne_one chi h3)
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_ne_one_of_pow_ne_one chi h4)
    ((mul_le_mul_of_nonneg_right hcq (by positivity)).trans hscale) hr
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc (by linarith) hz)

end LiuWang.Proof.Campaign20260915.OriginalRegion
