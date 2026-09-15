import LiuWang.Proof.Campaign20260915.ZetaWinding.PositiveCount
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

def logNormPrimitive (y x : ℝ) : ℝ :=
  if y = 0 then x * Real.log x - x
  else x / 2 * Real.log (x ^ 2 + y ^ 2) - x + y * Real.arctan (x / y)

theorem log_norm_horizontal (x y : ℝ) :
    Real.log ‖(x : ℂ) + (y : ℂ) * I‖ = Real.log (x ^ 2 + y ^ 2) / 2 := by
  have he : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [← normSq_eq_norm_sq]
    simp [normSq_apply, ← sq]
  have h := Real.log_pow ‖(x : ℂ) + (y : ℂ) * I‖ 2
  rw [he] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem logNormPrimitive_hasDerivAt {y : ℝ} (hy : y ≠ 0) (x : ℝ) :
    HasDerivAt (logNormPrimitive y) (Real.log ‖(x : ℂ) + (y : ℂ) * I‖) x := by
  have hq : x ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_pos_of_ne_zero hy, sq_nonneg x])
  have hl := (((hasDerivAt_id x).pow 2).add_const (y ^ 2)).log hq
  have ha := (((hasDerivAt_id x).div_const y).arctan).const_mul y
  have hd := ((((hasDerivAt_id x).div_const 2).mul hl).sub (hasDerivAt_id x)).add ha
  convert! hd using 1
  · funext u
    simp [logNormPrimitive, hy]
  · rw [log_norm_horizontal]
    norm_num only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp
    ring

theorem log_norm_horizontal_integrable (y a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖(x : ℂ) + (y : ℂ) * I‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  exact (show AnalyticAt ℝ (fun u : ℝ => (u : ℂ) + (y : ℂ) * I) x by
    exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const).meromorphicAt

theorem integral_log_norm_horizontal (y a b : ℝ) :
    (∫ x in a..b, Real.log ‖(x : ℂ) + (y : ℂ) * I‖) =
      logNormPrimitive y b - logNormPrimitive y a := by
  by_cases hy : y = 0
  · subst y
    simp only [ofReal_zero, zero_mul, add_zero, norm_real, Real.norm_eq_abs,
      Real.log_abs, logNormPrimitive, ↓reduceIte]
    rw [integral_log]
    ring
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => logNormPrimitive_hasDerivAt hy x) (log_norm_horizontal_integrable y a b)

theorem log_norm_zero_factor_integrable (rho : ℂ) (T a b : ℝ) :
    IntervalIntegrable (fun x => Real.log ‖horizontalAt T x - rho‖) volume a b := by
  have h := (log_norm_horizontal_integrable (T - rho.im) (a - rho.re) (b - rho.re)).comp_sub_right rho.re
  have he (x : ℝ) : horizontalAt T x - rho =
      ((x - rho.re : ℝ) : ℂ) + ((T - rho.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [horizontalAt]
  simpa only [sub_add_cancel, he] using h

theorem integral_log_norm_zero_factor (rho : ℂ) (T a b : ℝ) :
    (∫ x in a..b, Real.log ‖horizontalAt T x - rho‖) =
      logNormPrimitive (T - rho.im) (b - rho.re) -
        logNormPrimitive (T - rho.im) (a - rho.re) := by
  have he (x : ℝ) : horizontalAt T x - rho =
      ((x - rho.re : ℝ) : ℂ) + ((T - rho.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [horizontalAt]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_sub_right
    (fun x : ℝ => Real.log ‖(x : ℂ) + ((T - rho.im : ℝ) : ℂ) * I‖) rho.re,
    integral_log_norm_horizontal]

theorem integral_log_norm_zero_ratio (rho : ℂ) (T a b d : ℝ) :
    (∫ x in a..b, Real.log ‖(horizontalAt T x - rho) /
        (horizontalAt T (x + d) - rho)‖) =
      logNormPrimitive (T - rho.im) (b - rho.re) -
        logNormPrimitive (T - rho.im) (a - rho.re) -
      (logNormPrimitive (T - rho.im) (b + d - rho.re) -
        logNormPrimitive (T - rho.im) (a + d - rho.re)) := by
  have he : (∫ x in a..b, Real.log ‖(horizontalAt T x - rho) /
        (horizontalAt T (x + d) - rho)‖) =
      ∫ x in a..b, Real.log ‖horizontalAt T x - rho‖ -
        Real.log ‖horizontalAt T (x + d) - rho‖ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne rho.re, volume.ae_ne (rho.re - d)] with x hx hx' _
    have hn : horizontalAt T x - rho ≠ 0 := by
      intro hh
      have hr := congrArg Complex.re hh
      simp [horizontalAt] at hr
      exact hx (by linarith)
    have hd : horizontalAt T (x + d) - rho ≠ 0 := by
      intro hh
      have hr := congrArg Complex.re hh
      simp [horizontalAt] at hr
      exact hx' (by linarith)
    rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hn) (norm_ne_zero_iff.mpr hd)]
  have hi : IntervalIntegrable (fun x => Real.log ‖horizontalAt T (x + d) - rho‖)
      volume a b := by
    have h := (log_norm_zero_factor_integrable rho T (a + d) (b + d)).comp_add_right d
    simpa using h
  rw [he, intervalIntegral.integral_sub (log_norm_zero_factor_integrable rho T a b) hi,
    integral_log_norm_zero_factor, intervalIntegral.integral_comp_add_right
      (fun x : ℝ => Real.log ‖horizontalAt T x - rho‖) d,
    integral_log_norm_zero_factor]

theorem zeta_horizontal_log_integrable {T : ℝ} (hT : T ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun x => Real.log ‖riemannZeta (horizontalAt T x)‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  have hn : horizontalAt T x ≠ 1 := by
    intro hh
    have hi := congrArg Complex.im hh
    exact hT (by simpa [horizontalAt] using hi)
  have ha := (LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one hn).restrictScalars (𝕜 := ℝ)
  exact (ha.comp (show AnalyticAt ℝ (horizontalAt T) x by
    exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const)).meromorphicAt

theorem integral_finite_zero_log_contribution (F : Finset ℂ) (T a b : ℝ) :
    (∫ x in a..b, ∑ rho ∈ F,
      (analyticOrderNatAt riemannZeta rho : ℝ) * Real.log ‖horizontalAt T x - rho‖) =
      ∑ rho ∈ F, (analyticOrderNatAt riemannZeta rho : ℝ) *
        (logNormPrimitive (T - rho.im) (b - rho.re) -
          logNormPrimitive (T - rho.im) (a - rho.re)) := by
  rw [intervalIntegral.integral_finsetSum
    (fun rho _ => (log_norm_zero_factor_integrable rho T a b).const_mul _)]
  apply Finset.sum_congr rfl
  intro rho _
  rw [intervalIntegral.integral_const_mul, integral_log_norm_zero_factor]

#print axioms integral_log_norm_horizontal
#print axioms integral_log_norm_zero_ratio
#print axioms zeta_horizontal_log_integrable
#print axioms integral_finite_zero_log_contribution

end LiuWang.Proof.Campaign20260915.ZetaWinding
