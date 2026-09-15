import LiuWang.Proof.Campaign20260915.ZetaWinding.CountingIntegral

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.DirichletZeroCount

def xiLogCorrection (s : ℂ) : ℂ :=
  log s + log (s - 1) + gammaLogBranch (s / 2) -
    s / 2 * (Real.log Real.pi : ℂ)

theorem zeta_horizontal_regular {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : 1 / 2 ≤ x) : riemannZeta (horizontalAt T x) ≠ 0 := by
  by_cases h1 : x < 1
  · exact hr _ (by simp [horizontalAt]; linarith) (by simpa [horizontalAt] using h1)
      (by simp [horizontalAt, abs_of_pos hT])
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa [horizontalAt] using not_lt.mp h1)

theorem zeta_logDeriv_horizontal_continuousAt {T x : ℝ} (hT : T ≠ 0)
    (hz : riemannZeta (horizontalAt T x) ≠ 0) :
    ContinuousAt (fun u => logDeriv riemannZeta (horizontalAt T u)) x := by
  have hn : horizontalAt T x ≠ 1 := by
    intro he
    exact hT (by simpa [horizontalAt] using congrArg Complex.im he)
  have ha := LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one hn
  exact (ha.deriv.continuousAt.div ha.continuousAt hz).comp
    (f := horizontalAt T) (by unfold horizontalAt; fun_prop)

theorem zeta_logDeriv_horizontal_integrable {T a b : ℝ} (hT : T ≠ 0)
    (hz : ∀ x ∈ Set.uIcc a b, riemannZeta (horizontalAt T x) ≠ 0) :
    IntervalIntegrable (fun x => logDeriv riemannZeta (horizontalAt T x)) volume a b :=
  ContinuousOn.intervalIntegrable (fun x hx =>
    (zeta_logDeriv_horizontal_continuousAt hT (hz x hx)).continuousWithinAt)

theorem xiLogCorrection_hasDerivAt {s : ℂ} (hs : 0 < s.re)
    (ht : s - 1 ∈ slitPlane) (hz : riemannZeta s ≠ 0) :
    HasDerivAt xiLogCorrection (logDeriv riemannXi s - logDeriv riemannZeta s) s := by
  have hn : s ≠ 1 := by intro he; simp [he] at ht
  have hp : 0 < ((riemannZeta s)⁻¹ * riemannZeta s).re := by simp [hz]
  have hlocal := localXiPrimitive_hasDerivAt hs ht hp
  have hlog := ((differentiableAt_riemannZeta hn).hasDerivAt.const_mul
    (riemannZeta s)⁻¹).clog (mem_slitPlane_iff.mpr (Or.inl hp))
  have he : (riemannZeta s)⁻¹ * deriv riemannZeta s /
      ((riemannZeta s)⁻¹ * riemannZeta s) = logDeriv riemannZeta s := by
    rw [logDeriv_apply, mul_div_mul_left _ _ (inv_ne_zero hz)]
  rw [he] at hlog
  convert! hlocal.sub hlog using 1
  funext z
  dsimp [localXiPrimitive, xiLogCorrection]
  ring

theorem xiLogCorrection_horizontal_integral {T : ℝ} (hT : 0 < T)
    (hz : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2, riemannZeta (horizontalAt T x) ≠ 0) :
    HIntegral (logDeriv riemannXi) (1 / 2) 2 T -
      HIntegral (logDeriv riemannZeta) (1 / 2) 2 T =
        xiLogCorrection (horizontalAt T 2) - xiLogCorrection (horizontalAt T (1 / 2)) := by
  have hxi : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2, riemannXi (horizontalAt T x) ≠ 0 := by
    intro x hx h0
    have hx' : 1 / 2 ≤ x := by
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact hx.1
    have hn : horizontalAt T x ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp [horizontalAt] at hi
      linarith
    exact hz x hx ((LiuWang.Proof.PrincipalPsi.Quantitative.xi_zero_iff_zeta_zero
      (by simp [horizontalAt]; linarith) hn).mp h0)
  have hi : IntervalIntegrable (fun x => logDeriv riemannXi (horizontalAt T x))
      volume (1 / 2) 2 := by
    simpa [horizontalAt, add_comm] using
      xi_line_integrable (a := 1 / 2) (b := 2) ((T : ℂ) * I) 1
        (by simpa [horizontalAt, add_comm] using hxi)
  have hzI := zeta_logDeriv_horizontal_integrable hT.ne' hz
  change (∫ x in (1 / 2 : ℝ)..2, logDeriv riemannXi (horizontalAt T x)) -
    (∫ x in (1 / 2 : ℝ)..2, logDeriv riemannZeta (horizontalAt T x)) = _
  rw [← intervalIntegral.integral_sub hi hzI]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => xiLogCorrection (horizontalAt T x)) _ (hi.sub hzI)
  intro x hx
  have hx' : 1 / 2 ≤ x := by
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact hx.1
  have hd := xiLogCorrection_hasDerivAt
    (by simp [horizontalAt]; linarith : 0 < (horizontalAt T x).re)
    (mem_slitPlane_iff.mpr (Or.inr (by simpa [horizontalAt] using hT.ne'))) (hz x hx)
  simpa [horizontalAt, Function.comp_def, smul_eq_mul] using
    hd.scomp x ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((T : ℂ) * I))

theorem critical_polynomial_argument_positive {T : ℝ} (hT : 0 < T) :
    (log (criticalPoint T)).im + (log (criticalPoint T - 1)).im = Real.pi := by
  have he : criticalPoint T - 1 = -conj (criticalPoint T) := by
    apply Complex.ext <;> norm_num [criticalPoint]
  have hp : (criticalPoint T).arg ≠ Real.pi := by
    have h := arg_lt_pi_div_two_iff.mpr
      (Or.inl (by norm_num [criticalPoint] : 0 < (criticalPoint T).re))
    linarith [Real.pi_pos]
  rw [he, log_im, log_im, arg_neg_eq_arg_add_pi_of_im_neg
    (by simpa [criticalPoint] using neg_neg_of_pos hT :
      (conj (criticalPoint T)).im < 0), arg_conj, if_neg hp]
  ring

theorem xiLogCorrection_critical_im {T : ℝ} (hT : 0 < T) :
    (xiLogCorrection (horizontalAt T (1 / 2))).im =
      Real.pi + criticalGammaArgument T := by
  have he : horizontalAt T (1 / 2) = criticalPoint T := by
    apply Complex.ext <;> norm_num [horizontalAt, criticalPoint]
  rw [he]
  have hp := critical_polynomial_argument_positive hT
  dsimp [xiLogCorrection, criticalGammaArgument] at *
  linarith

theorem turingS_eq_horizontal_logDeriv {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    Real.pi * turingS T =
      (log (riemannZeta (horizontalAt T 2)) -
        HIntegral (logDeriv riemannZeta) (1 / 2) 2 T).im := by
  have hz : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2, riemannZeta (horizontalAt T x) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact zeta_horizontal_regular hT hr hx.1
  have hc := Argument.principal_count_eq_upper_im 1 (b := 2) (by norm_num) hT.le
    (by simpa only [DirichletCharacter.LFunction_modOne_eq] using hr)
  rw [← zetaClosedCount_eq_principal, zetaClosedCount_eq_two_positiveCount] at hc
  push_cast at hc
  rw [Argument.upperRightIntegral, xi_right_vertical_primitive_all,
    sub_im, sub_im, xiCountingPrimitive_two_im, sub_zero] at hc
  have hi := congrArg Complex.im (xiLogCorrection_horizontal_integral hT hz)
  rw [sub_im, sub_im, xiLogCorrection_critical_im hT] at hi
  have he : xiCountingPrimitive (horizontalAt T 2) =
      log (riemannZeta (horizontalAt T 2)) + xiLogCorrection (horizontalAt T 2) := by
    dsimp [xiCountingPrimitive, xiLogCorrection]
    ring
  rw [he, add_im] at hc
  have hc' := (eq_div_iff Real.pi_ne_zero).mp hc
  dsimp [turingS]
  field_simp
  nlinarith

#print axioms xiLogCorrection_horizontal_integral
#print axioms critical_polynomial_argument_positive
#print axioms turingS_eq_horizontal_logDeriv

end LiuWang.Proof.Campaign20260915.ZetaWinding
