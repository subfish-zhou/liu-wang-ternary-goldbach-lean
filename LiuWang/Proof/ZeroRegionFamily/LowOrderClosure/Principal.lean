import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.High

/-! # 模1实际四次正性与xi重数核支付主字符R14 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure

namespace LiuWang.Proof.ZeroRegionFamily.LowOrderClosure

theorem zeta_quartic_core (p : RiemannXiDivisorZeroIndex)
    (hr : 1/2 < (riemannXiDivisorZeroValue p).re)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    24480/(sigma-(riemannXiDivisorZeroValue p).re) ≤ 14379/(sigma-1)+
      46630*stechkinConductorCoeff*Real.log |(riemannXiDivisorZeroValue p).im|+139890 := by
  let t := (riemannXiDivisorZeroValue p).im
  have ht : 1 ≤ |t| := (xi_zero_height_gt_one p).le
  have hpos := quartic_stechkin_nonneg (1 : DirichletCharacter ℂ 1) hs t
  simp only [one_pow, dampedLogDeriv, DirichletCharacter.LFunction_modOne_eq] at hpos
  change 0 ≤ 14379*zetaDamped sigma 0+24480*zetaDamped sigma t+
    14900*zetaDamped sigma (2*t)+6000*zetaDamped sigma (3*t)+1250*zetaDamped sigma (4*t) at hpos
  have hmain := zeta_selected_high p hr hs hs1
  change zetaDamped sigma t+_ ≤ _ at hmain
  have h0 := zeta_real_strong hs hs1
  have hj (j : ℝ) (hj : 1 ≤ j) : 1 ≤ |j*t| := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    nlinarith
  have h2 := zeta_high hs hs1 (hj 2 (by norm_num))
  have h3 := zeta_high hs hs1 (hj 3 (by norm_num))
  have h4 := zeta_high hs hs1 (hj 4 (by norm_num))
  have hl (j : ℕ) (hj1 : 1 ≤ j) :
      stechkinConductorCoeff*Real.log |(j : ℝ)*t| ≤
        stechkinConductorCoeff*(Real.log |t|+(j : ℝ)-1) := by
    have hh := log_max_harmonic_le t hj1
    rw [max_eq_right ht, max_eq_right (hj _ (by exact_mod_cast hj1))] at hh
    exact mul_le_mul_of_nonneg_left hh conductorCoeff_bounds.1
  have hl2 := hl 2 (by norm_num)
  have hl3 := hl 3 (by norm_num)
  have hl4 := hl 4 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hl2 hl3 hl4
  have hp := mul_le_mul_of_nonneg_left log_pi_ge_one conductorCoeff_bounds.1
  have hk := stechkinK_mem.1
  have hc := conductorCoeff_bounds
  change 24480/(sigma-(riemannXiDivisorZeroValue p).re) ≤
    14379/(sigma-1)+46630*stechkinConductorCoeff*Real.log |t|+139890
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem zeta_no_zero_fourteen {x : ℝ} (hx : 160 ≤ Real.log x) {rho : ℂ}
    (hr : 1-1/(14*Real.log x) < rho.re) (ht : |rho.im| ≤ x) : riemannZeta rho ≠ 0 := by
  have hL : 0 < Real.log x := by linarith
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  intro hz
  obtain ⟨p, hv⟩ := exists_xi_index_of_zeta_zero (by linarith) hz
  have hb := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
  have ht1 := xi_zero_height_gt_one p
  rw [hv] at hb ht1
  let u := (27/100)/Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by
    dsimp [u]
    apply (div_le_iff₀ hL).mpr
    linarith
  have huL : Real.log x*u=27/100 := by dsimp [u]; field_simp
  have hh := zeta_quartic_core p (by rw [hv]; linarith)
    (sigma := 1+u) (by linarith) (by linarith)
  rw [hv] at hh
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith : 0 < |rho.im|) ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL.le
  have hinv : 14379/(1+u-1)=(14379/(27/100))*Real.log x := by dsimp [u]; field_simp; ring
  rw [hinv] at hh
  have hupp : 24480/(1+u-rho.re) ≤
      (14379/(27/100)+46630*(691/2500)+139890/160)*Real.log x := by nlinarith only [hh, hl, hk, hx]
  have hp := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 1/14 := by
    have hh := (lt_div_iff₀ (show 0 < 14*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(14*Real.log x) by linarith)
    nlinarith only [hh]
  nlinarith only [hp, hgap, huL]

theorem principal_no_zero_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 160 ≤ Real.log x) {rho : ℂ}
    (hr : 1-1/(14*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ)) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction rho ≠ 0 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hx0 : 0 ≤ x := by
    have hh : 0 ≤ x/(q : ℝ) := (abs_nonneg _).trans ht
    have hh' := mul_nonneg hh (show (0 : ℝ) ≤ q by positivity)
    simpa only [div_mul_cancel₀ _ (show (q : ℝ) ≠ 0 by positivity)] using hh'
  have hheight := ht.trans (div_le_self hx0 hq)
  have hw : 1/(14*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  exact fun hz => zeta_no_zero_fourteen hx hr hheight
    ((PrincipalPsi.principal_zero_iff_zeta_zero (by linarith) hpole).mp hz)

end LiuWang.Proof.ZeroRegionFamily.LowOrderClosure
