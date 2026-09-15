import LiuWang.Proof.Campaign20260915.OriginalRegion.LectureScalar
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CaseIV

/-! The independent principal branch uses actual xi zeros, not a nonprincipal surrogate. -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1 (lwd_log_pi)

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem zeta_lecture_budget (p : RiemannXiDivisorZeroIndex)
    (hr : 1 / 2 < (riemannXiDivisorZeroValue p).re)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    19.073344004352 / (sigma - (riemannXiDivisorZeroValue p).re) ≤
      11.1859355312082048 / (sigma - 1) +
        36.506331844352 * stechkinConductorCoeff *
          Real.log |(riemannXiDivisorZeroValue p).im| := by
  let t := (riemannXiDivisorZeroValue p).im
  have ht : 1 ≤ |t| := (xi_zero_height_gt_one p).le
  have hpos := lecture_damped_nonneg (1 : DirichletCharacter ℂ 1) hs t
  simp only [one_pow, dampedLogDeriv, DirichletCharacter.LFunction_modOne_eq] at hpos
  change 0 ≤ 11.1859355312082048 * zetaDamped sigma 0 +
    19.073344004352 * zetaDamped sigma t +
    11.67618784 * zetaDamped sigma (2 * t) +
    4.7568 * zetaDamped sigma (3 * t) + zetaDamped sigma (4 * t) at hpos
  have hmain := zeta_selected_high p hr hs hs1
  change zetaDamped sigma t + _ ≤ _ at hmain
  have hzero := zeta_real_strong hs hs1
  have hj (j : ℝ) (hj : 1 ≤ j) : 1 ≤ |j * t| := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    nlinarith
  have h2 := zeta_high hs hs1 (hj 2 (by norm_num))
  have h3 := zeta_high hs hs1 (hj 3 (by norm_num))
  have h4 := zeta_high hs hs1 (hj 4 (by norm_num))
  have hl (j : ℕ) (hj1 : 1 ≤ j) :
      stechkinConductorCoeff * Real.log |(j : ℝ) * t| ≤
        stechkinConductorCoeff * (Real.log |t| + Real.log j) := by
    have hh := log_max_multiple (t := t) hj1
    rw [max_eq_right ht, max_eq_right (hj _ (by exact_mod_cast hj1))] at hh
    exact mul_le_mul_of_nonneg_left hh conductorCoeff_bounds.1
  have hl2 := hl 2 (by norm_num)
  have hl3 := hl 3 (by norm_num)
  have hl4 := hl 4 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hl2 hl3 hl4
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hl4
  have hpi := mul_le_mul_of_nonneg_left lwd_log_pi conductorCoeff_bounds.1
  have hl2u := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le conductorCoeff_bounds.1
  have hl3u := mul_le_mul_of_nonneg_left Real.log_three_lt_d9.le conductorCoeff_bounds.1
  have hk := stechkinK_ge
  have hc : 11 / 40 ≤ stechkinConductorCoeff := by
    dsimp [stechkinConductorCoeff]
    linarith [stechkinK_le]
  have hc1 := conductorCoeff_bounds.2
  change 19.073344004352 / (sigma - (riemannXiDivisorZeroValue p).re) ≤
    11.1859355312082048 / (sigma - 1) +
      36.506331844352 * stechkinConductorCoeff * Real.log |t|
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem zeta_original_no_zero_closed {x : ℝ} (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (ht : |rho.im| ≤ x) : riemannZeta rho ≠ 0 := by
  intro hz
  have hlog := log_scale_ge_34_15 hx
  have hL : 0 < Real.log x := by linarith
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / 10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  obtain ⟨p, hv⟩ := exists_xi_index_of_zeta_zero (by linarith) hz
  have hb := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
  have ht1 := xi_zero_height_gt_one p
  rw [hv] at hb ht1
  obtain ⟨hA, hAm, _⟩ := lectureShift_properties
  let u := lectureShift / Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3 / 20 := by
    apply (div_le_iff₀ hL).mpr
    linarith
  have hh := zeta_lecture_budget p (by rw [hv]; linarith)
    (sigma := 1 + u) (by linarith) (by linarith)
  rw [hv] at hh
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_log (by linarith : 0 < |rho.im|) ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 36.506331844352) conductorCoeff_bounds.1)
  have hpaid : 19.073344004352 / (1 + u - rho.re) ≤
      11.1859355312082048 / u + 36.506331844352 * stechkinConductorCoeff * Real.log x := by
    norm_num only [add_sub_cancel_left] at hh
    linarith
  have hgap : (1 - rho.re) * Real.log x ≤ 1 / 9.645908801 := by
    have hh := (le_div_iff₀ (show 0 < 9.645908801 * Real.log x by positivity)).mp
      (show 1 - rho.re ≤ 1 / (9.645908801 * Real.log x) by linarith)
    nlinarith only [hh]
  exact lecture_scaled_budget_contradiction hL hb hgap hpaid

theorem principal_original_no_zero_closed {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (ht : |rho.im| ≤ x / q) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction rho ≠ 0 := by
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / 10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [log_scale_ge_34_15 hx]
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  exact fun hz => zeta_original_no_zero_closed hx hr (ht.trans (div_le_self (by linarith) hq))
    ((PrincipalPsi.principal_zero_iff_zeta_zero (by linarith) hpole).mp hz)

theorem zeta_original_no_zero {x : ℝ} (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re)
    (ht : |rho.im| ≤ x) : riemannZeta rho ≠ 0 :=
  zeta_original_no_zero_closed hx hr.le ht

theorem principal_original_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re)
    (ht : |rho.im| ≤ x / q) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction rho ≠ 0 :=
  principal_original_no_zero_closed hx hr.le ht hpole

end LiuWang.Proof.Campaign20260915.OriginalRegion
