import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalNonzero
import LiuWang.Proof.Campaign20260915.ZetaValidation.GammaPhase16
import LiuWang.Proof.DirichletZeroCount.Remainder.LogGamma
import LiuWang.Proof.DirichletZeroCount.Remainder.XiVertical

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def xiCountingPrimitive (s : ℂ) : ℂ :=
  log (riemannZeta s) + log s + log (s - 1) +
    gammaLogBranch (s / 2) - s / 2 * (Real.log Real.pi : ℂ)

theorem xiCountingPrimitive_hasDerivAt {s : ℂ} (hs : 0 < s.re)
    (hslit : s - 1 ∈ slitPlane) (hz : 0 < (riemannZeta s).re) :
    HasDerivAt xiCountingPrimitive (logDeriv riemannXi s) s := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hs1 : s ≠ 1 := by
    intro he
    simp [he] at hslit
  have hsz : riemannZeta s ≠ 0 := ne_zero_of_re_pos hz
  have hlz := (differentiableAt_riemannZeta hs1).hasDerivAt.clog
    (mem_slitPlane_iff.mpr (Or.inl hz))
  have hls := hasDerivAt_log (mem_slitPlane_iff.mpr (Or.inl hs))
  have hl1 := ((hasDerivAt_id s).sub_const 1).clog hslit
  have hg : HasDerivAt (fun w : ℂ => gammaLogBranch (w / 2))
      ((1 / 2 : ℂ) * digamma (s / 2)) s := by
    have h := LiuWang.Proof.DirichletZeroCount.Remainder.logGamma_hasDerivAt
      (z := s / 2) (by simpa using half_pos hs)
    simpa only [gammaLogBranch, LiuWang.Proof.DirichletZeroCount.Remainder.logGamma,
      Function.comp_def, id_eq, mul_comm] using! h.comp s ((hasDerivAt_id s).div_const 2)
  have hd := (((hlz.add hls).add hl1).add hg).sub
    (((hasDerivAt_id s).div_const 2).mul_const (Real.log Real.pi : ℂ))
  have hx := LiuWang.Proof.PrincipalPsi.Quantitative.logDeriv_xi_eq_zeta
    (by linarith : -2 < s.re) hs1 hsz
  have hgam : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m he
    have hr := congrArg Complex.re he
    simp only [div_ofNat_re, neg_re, natCast_re] at hr
    linarith [Nat.cast_nonneg m (α := ℝ)]
  rw [digamma_apply_add_one (s / 2) hgam] at hx
  have hder : deriv riemannZeta s / riemannZeta s + s⁻¹ +
      1 / (s - 1) + (1 / 2 : ℂ) * digamma (s / 2) -
        (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) = logDeriv riemannXi s := by
    rw [hx, logDeriv_apply]
    field_simp
    ring
  change HasDerivAt xiCountingPrimitive
    (deriv riemannZeta s / riemannZeta s + s⁻¹ + 1 / (s - 1) +
      1 / 2 * digamma (s / 2) - 1 / 2 * (Real.log Real.pi : ℂ)) s at hd
  rw [hder] at hd
  exact hd

private theorem xi_path_integrable {a b : ℝ} (z v : ℂ)
    (hn : ∀ t ∈ Set.uIcc a b, riemannXi (z + (t : ℂ) * v) ≠ 0) :
    IntervalIntegrable (fun t : ℝ => v * logDeriv riemannXi (z + (t : ℂ) * v)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ha := differentiable_riemannXi.analyticAt (z + (t : ℂ) * v)
  have hc := (ha.deriv.div ha (hn t ht)).continuousAt.comp
    (f := fun x : ℝ => z + (x : ℂ) * v) (by fun_prop)
  simpa only [logDeriv_apply, Function.comp_def, Pi.div_apply, Pi.mul_apply] using!
    ((continuousAt_const (y := v)).mul hc).continuousWithinAt

theorem xi_upper_horizontal_primitive :
    HIntegral (logDeriv riemannXi) (1 / 2) 2 16 =
      xiCountingPrimitive (horizontalPoint 2) - xiCountingPrimitive (criticalPoint 16) := by
  have hd (x : ℝ) (hx : x ∈ Set.uIcc (1 / 2 : ℝ) 2) :
      HasDerivAt (fun u : ℝ => xiCountingPrimitive (horizontalPoint u))
        (logDeriv riemannXi (horizontalPoint x)) x := by
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have h := xiCountingPrimitive_hasDerivAt (s := horizontalPoint x)
      (by simpa [horizontalPoint] using (show 0 < x by linarith [hx.1]))
      (mem_slitPlane_iff.mpr (Or.inr (by norm_num [horizontalPoint])))
      (horizontal_zeta_re_pos hx.1)
    have hline : HasDerivAt horizontalPoint 1 x := by
      have he : horizontalPoint = (fun u : ℝ => (u : ℂ) + 16 * I) := by
        funext u
        apply Complex.ext <;> norm_num [horizontalPoint]
      rw [he]
      simpa using!
        (Complex.ofRealCLM.hasDerivAt (x := x)).add_const (16 * I)
    simpa only [Function.comp_def, smul_eq_mul, one_mul] using h.scomp x hline
  have hi := xi_path_integrable (a := 1 / 2) (b := 2) (16 * I) 1 (fun t ht => by
    have hp : 1 / 2 ≤ t := by rw [Set.uIcc_of_le (by norm_num)] at ht; exact ht.1
    intro hz
    have hs := LiuWang.Proof.DirichletZeroCount.Argument.xi_zero_strip hz
    have hzn := (LiuWang.Proof.PrincipalPsi.Quantitative.xi_zero_iff_zeta_zero
      (by simpa using (show -2 < t by linarith)) (by intro he; have := congrArg Complex.im he; norm_num at this)).mp hz
    exact zeta_ne_zero_horizontal_right (by simpa using hp) (by norm_num) hzn)
  have hi' : IntervalIntegrable (fun t => logDeriv riemannXi (horizontalPoint t))
      volume (1 / 2) 2 := by
    simpa only [one_mul, mul_one, horizontalPoint, Complex.mk_eq_add_mul_I, add_comm,
      ofReal_ofNat] using hi
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi'
  simpa only [HIntegral, horizontalPoint, criticalPoint, Complex.mk_eq_add_mul_I,
    ofReal_ofNat, ofReal_div] using he

theorem xi_right_vertical_primitive :
    VIntegral (logDeriv riemannXi) 2 0 16 =
      xiCountingPrimitive (horizontalPoint 2) - xiCountingPrimitive 2 := by
  have hd (t : ℝ) :
      HasDerivAt (fun u : ℝ => xiCountingPrimitive (2 + (u : ℂ) * I))
        (I * logDeriv riemannXi (2 + (t : ℂ) * I)) t := by
    have hz := LiuWang.Proof.DirichletZeroCount.Remainder.LFunction_re_pos
      (1 : LiuWang.Proof.Interfaces.Character 1)
      (s := 2 + (t : ℂ) * I) (by norm_num)
    rw [DirichletCharacter.LFunction_modOne_eq] at hz
    have h := xiCountingPrimitive_hasDerivAt (s := 2 + (t : ℂ) * I)
      (by norm_num) (mem_slitPlane_iff.mpr (Or.inl (by norm_num))) hz
    simpa only [LiuWang.Proof.DirichletZeroCount.Argument.linePoint, Function.comp_def,
      smul_eq_mul] using
      h.scomp t (LiuWang.Proof.DirichletZeroCount.Argument.line_hasDerivAt 2 I t)
  have hi := LiuWang.Proof.DirichletZeroCount.Remainder.xi_vertical_integrable 16
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at he
  simpa [VIntegral, horizontalPoint, Complex.mk_eq_add_mul_I, smul_eq_mul] using he

theorem xi_upper_integral_primitive :
    LiuWang.Proof.DirichletZeroCount.Argument.upperRightIntegral (logDeriv riemannXi) 2 16 =
      xiCountingPrimitive (criticalPoint 16) - xiCountingPrimitive 2 := by
  rw [LiuWang.Proof.DirichletZeroCount.Argument.upperRightIntegral,
    xi_right_vertical_primitive, xi_upper_horizontal_primitive]
  ring

#print axioms xi_upper_integral_primitive

end LiuWang.Proof.Campaign20260915.ZetaValidation
