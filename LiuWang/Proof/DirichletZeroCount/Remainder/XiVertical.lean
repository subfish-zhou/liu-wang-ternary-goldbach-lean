import LiuWang.Proof.DirichletZeroCount.Remainder.FamilyPhase
import LiuWang.Proof.DirichletZeroCount.Argument.UpperHalf

/-! # A separate actual xi right-edge payment, including the polynomial factor -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def xiRightPrimitive (t : ℝ) : ℂ :=
  log (1 + (t : ℂ) * I) + logGamma (2 + (t : ℂ) * I / 2) -
    ((t * Real.log Real.pi / 2 : ℝ) : ℂ) * I

theorem xiRightPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt xiRightPrimitive
      (I * logDeriv riemannXi (2 + (t : ℂ) * I) -
        I * logDeriv riemannZeta (2 + (t : ℂ) * I)) t := by
  have hlog := ((Argument.line_hasDerivAt 1 I t).clog_real
    (by apply mem_slitPlane_iff.mpr; left; norm_num [Argument.linePoint]))
  have hgamma := (logGamma_hasDerivAt (z := 2 + (t : ℂ) * I / 2) (by norm_num)).scomp t
    (((Complex.ofRealCLM.hasDerivAt).mul_const I).div_const 2 |>.const_add 2)
  have hpi := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).mul_const (Real.log Real.pi)).div_const 2)).mul_const I
  have he := PrincipalPsi.Quantitative.logDeriv_xi_eq_zeta
    (s := 2 + (t : ℂ) * I) (by norm_num)
    (by intro hh; have hr := congrArg Complex.re hh; norm_num at hr)
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hd := (hlog.add hgamma).sub hpi
  convert! hd using 1
  rw [he]
  simp only [Argument.linePoint, smul_eq_mul, ofRealCLM_apply,
    one_mul, ofReal_div, ofReal_ofNat, ofReal_one]
  rw [show (2 + (t : ℂ) * I) / 2 + 1 = 2 + (t : ℂ) * I / 2 by ring]
  ring

theorem xi_vertical_integrable (H : ℝ) :
    IntervalIntegrable (fun t : ℝ => I * logDeriv riemannXi (2 + (t : ℂ) * I)) volume 0 H := by
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro t
  have hn : riemannXi (2 + (t : ℂ) * I) ≠ 0 := by
    intro hh
    have hr := (Argument.xi_zero_strip hh).2
    norm_num at hr
  have ha := differentiable_riemannXi.analyticAt (2 + (t : ℂ) * I)
  have hc := (ha.deriv.div ha hn).continuousAt.comp
    (f := fun x : ℝ => (2 : ℂ) + (x : ℂ) * I) (by fun_prop)
  simpa only [logDeriv_apply, Function.comp_def, Pi.div_apply, Pi.mul_apply] using!
    (continuousAt_const (y := I)).mul hc

theorem xi_vertical_split (H : ℝ) :
    VIntegral (logDeriv riemannXi) 2 0 H =
      VIntegral (logDeriv riemannZeta) 2 0 H +
        xiRightPrimitive H - xiRightPrimitive 0 := by
  have hz : IntervalIntegrable (fun t : ℝ => I * logDeriv riemannZeta (2 + (t : ℂ) * I))
      volume 0 H := by
    simpa only [DirichletCharacter.LFunction_modOne_eq, ofReal_ofNat] using
      (vertical_L_logDeriv_continuous (1 : Character 1) (b := 2) le_rfl).intervalIntegrable 0 H
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => xiRightPrimitive_hasDerivAt t)
    ((xi_vertical_integrable H).sub hz)
  rw [intervalIntegral.integral_sub (xi_vertical_integrable H) hz] at he
  simp only [intervalIntegral.integral_const_mul] at he
  simpa only [VIntegral, smul_eq_mul, ofReal_ofNat] using (sub_eq_iff_eq_add.mp he).trans (by ring)

theorem logGamma_real_im_zero {x : ℝ} (hx : 0 < x) : (logGamma (x : ℂ)).im = 0 := by
  have he := congrArg Complex.im (logGamma_conjugate (z := (x : ℂ)) hx)
  simp only [conj_ofReal, conj_im] at he
  linarith

theorem xiRightPrimitive_im_le {H : ℝ} (hH : 0 ≤ H) :
    (xiRightPrimitive H - xiRightPrimitive 0).im ≤
      Real.pi / 2 + sourceGammaMain 4 H / 2 - H * Real.log Real.pi / 2 := by
  have hg := logGamma_im_le_stirling (z := ((4 : ℂ) + (H : ℂ) * I) / 2)
    (by norm_num) (by simpa using div_nonneg hH (by norm_num : (0 : ℝ) ≤ 2))
  have he : ((4 : ℂ) + (H : ℂ) * I) / 2 = 2 + (H : ℂ) * I / 2 := by ring
  have hmain := gammaPhaseMain_eq_source (a := 4) (H := H) (by norm_num)
  unfold gammaPhaseMain at hmain
  norm_num only [ofReal_ofNat] at hmain
  rw [he] at hg hmain
  have hp := (abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (by norm_num : 0 < (1 + (H : ℂ) * I).re))).le
  have harg := (le_abs_self (1 + (H : ℂ) * I).arg).trans hp
  have hzero : (logGamma (2 : ℂ)).im = 0 := logGamma_real_im_zero (x := 2) (by norm_num)
  simp only [xiRightPrimitive, sub_im, add_im, log_im, mul_im,
    ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero,
    ofReal_zero, zero_mul, zero_div, log_one, zero_im, sub_zero, hzero]
  linarith

theorem principal_count_le_xi_horizontal (q : ℕ) [NeZero q] {H : ℝ} (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H →
      (1 : Character q).LFunction s ≠ 0) :
    (count (1 : Character q) 0 H : ℝ) ≤
      (3 * Real.pi + sourceGammaMain 4 H - H * Real.log Real.pi -
        2 * (HIntegral (logDeriv riemannXi) (1 / 2) 2 H).im) / Real.pi := by
  have hz := vertical_L_im_abs_lt_pi (1 : Character 1) (b := 2) le_rfl 0 H
  simp only [DirichletCharacter.LFunction_modOne_eq] at hz
  have hx := xiRightPrimitive_im_le hH
  rw [Argument.principal_count_eq_upper_im q (b := 2) (by norm_num) hH hreg]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  rw [Argument.upperRightIntegral, xi_vertical_split]
  simp only [sub_im, add_im] at hx ⊢
  have hh := (le_abs_self _).trans hz.le
  linarith

end LiuWang.Proof.DirichletZeroCount.Remainder
