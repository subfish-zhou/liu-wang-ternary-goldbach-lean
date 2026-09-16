import LiuWang.Proof.Campaign20260915.RosserCount.BacklundCountIntegral
import LiuWang.Proof.Campaign20260915.ZetaWinding.LogDifferentiation
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Filter MeasureTheory
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.DirichletZeroCount
open BombieriVinogradov.SiegelWalfisz

theorem norm_logDeriv_zeta_le_real_negative_part {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv riemannZeta s‖ ≤ -(logDeriv riemannZeta (s.re : ℂ)).re := by
  let v : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  calc
    _ = ‖LSeries v s‖ := by
      rw [he]
      simp only [logDeriv_apply, norm_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term v s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ = vonMangoldtLSeriesNormSum s.re := by
      apply tsum_congr
      intro n
      simp only [LSeries.norm_term_eq, ofReal_re, v]
    _ = _ := by
      rw [vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re hs]
      simp only [logDeriv_apply, neg_div, neg_re]

private theorem right_logDeriv_continuousAt (T : ℝ) {x : ℝ} (hx : 1 < x) :
    ContinuousAt (fun u => logDeriv riemannZeta (horizontalAt T u)) x := by
  have hs : 1 < (horizontalAt T x).re := by simpa [horizontalAt] using hx
  have hn : horizontalAt T x ≠ 1 := by
    intro he
    simp [he] at hs
  have ha := LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one hn
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  simpa only [logDeriv_apply, Function.comp_def, Pi.div_apply] using
    ((ha.deriv.continuousAt.div ha.continuousAt hz).comp
      (f := horizontalAt T) (by unfold horizontalAt; fun_prop))

private theorem right_logDeriv_integrable (T : ℝ) {a b : ℝ}
    (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun u => logDeriv riemannZeta (horizontalAt T u)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  exact (right_logDeriv_continuousAt T ((lt_min ha hb).trans_le hx.1)).continuousWithinAt

theorem zeta_real_log_norm_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun u : ℝ => Real.log ‖riemannZeta (u : ℂ)‖)
      (logDeriv riemannZeta (x : ℂ)).re x := by
  have hs : 1 < (x : ℂ).re := by simpa using hx
  have hn : (x : ℂ) ≠ 1 := by intro he; simp [he] at hs
  have hd := (differentiableAt_riemannZeta hn).hasDerivAt.scomp x
    (Complex.ofRealCLM.hasDerivAt (x := x))
  simpa [logDeriv_apply, Function.comp_def, smul_eq_mul] using
    log_norm_hasDerivAt hd (riemannZeta_ne_zero_of_one_lt_re hs)

theorem backlundLog_right_reference (T : ℝ) {a b : ℝ}
    (ha : 1 < a) (hb : 2 ≤ b) :
    backlundLog T a =
      Complex.log (riemannZeta (horizontalAt T b)) -
        HIntegral (logDeriv riemannZeta) a b T := by
  have hi := right_logDeriv_integrable T (by norm_num : (1 : ℝ) < 2)
    (by linarith : 1 < b)
  have he : HIntegral (logDeriv riemannZeta) 2 b T =
      Complex.log (riemannZeta (horizontalAt T b)) -
        Complex.log (riemannZeta (horizontalAt T 2)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    simpa [horizontalAt, Function.comp_def, smul_eq_mul] using
      (log_zeta_hasDerivAt_right (s := horizontalAt T x)
        (by simpa [horizontalAt] using hx.1)).scomp x
        ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((T : ℂ) * I))
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (right_logDeriv_integrable T ha (by norm_num : (1 : ℝ) < 2)) hi
  change HIntegral (logDeriv riemannZeta) a 2 T +
    HIntegral (logDeriv riemannZeta) 2 b T = HIntegral (logDeriv riemannZeta) a b T at hadd
  unfold backlundLog
  rw [he] at hadd
  linear_combination -hadd

private theorem backlundLog_finite_norm_bound (T : ℝ) {a b : ℝ}
    (ha : 1 < a) (ha2 : a ≤ 2) (hb : 2 ≤ b) :
    ‖backlundLog T a‖ ≤ ‖Complex.log (riemannZeta (horizontalAt T b))‖ +
      Real.log ‖riemannZeta (a : ℂ)‖ - Real.log ‖riemannZeta (b : ℂ)‖ := by
  let M (x : ℝ) := -(logDeriv riemannZeta (x : ℂ)).re
  have hab : a ≤ b := ha2.trans hb
  have hb1 : 1 < b := by linarith
  have hi := right_logDeriv_integrable T ha hb1
  have hM : IntervalIntegrable M volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hh := right_logDeriv_continuousAt 0 ((lt_min ha hb1).trans_le hx.1)
    simpa only [M, horizontalAt, ofReal_zero, zero_mul, add_zero,
      Function.comp_def, Pi.neg_apply] using!
      ((Complex.continuous_re.continuousAt.comp hh).neg).continuousWithinAt
  have hbound : ‖HIntegral (logDeriv riemannZeta) a b T‖ ≤ ∫ x in a..b, M x := by
    have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab
      (f := fun x => logDeriv riemannZeta (horizontalAt T x))
    refine hn.trans (intervalIntegral.integral_mono_on hab hi.norm hM ?_)
    intro x hx
    simpa only [horizontalAt, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, M] using
      norm_logDeriv_zeta_le_real_negative_part
        (s := horizontalAt T x) (by simpa [horizontalAt] using ha.trans_le hx.1)
  have hMi : (∫ x in a..b, M x) =
      Real.log ‖riemannZeta (a : ℂ)‖ - Real.log ‖riemannZeta (b : ℂ)‖ := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => (zeta_real_log_norm_hasDerivAt
        ((lt_min ha hb1).trans_le hx.1)).neg) hM
    simpa only [Pi.neg_apply, neg_sub_neg, M] using he
  rw [hMi] at hbound
  rw [backlundLog_right_reference T ha hb]
  exact (norm_sub_le _ _).trans (by linarith only [hbound])

theorem norm_backlundLog_le_real_log_zeta (T : ℝ) {a : ℝ}
    (ha : 1 < a) (ha2 : a ≤ 2) :
    ‖backlundLog T a‖ ≤ Real.log ‖riemannZeta (a : ℂ)‖ := by
  have hr : Tendsto (fun b : ℝ => Real.log ‖riemannZeta (b : ℂ)‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, horizontalAt, ofReal_zero, zero_mul, add_zero, Complex.log_re,
      zero_re] using (Complex.continuous_re.tendsto 0).comp (log_zeta_horizontal_tendsto_zero 0)
  have ht := (((log_zeta_horizontal_tendsto_zero T).norm).add_const
    (Real.log ‖riemannZeta (a : ℂ)‖)).sub hr
  simp only [norm_zero, zero_add, sub_zero] at ht
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with b hb
  exact backlundLog_finite_norm_bound T ha ha2 hb

theorem positiveCount_backlund_real_log_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi +
      4 / (Real.pi * T) + |rosserGammaRemainder T| / Real.pi := by
  have hp : |(backlundLog T (5 / 4)).im| ≤ Real.log ‖riemannZeta (5 / 4 : ℂ)‖ := by
    have hh := (abs_im_le_norm (backlundLog T (5 / 4))).trans
      (norm_backlundLog_le_real_log_zeta T (by norm_num : (1 : ℝ) < 5 / 4)
        (by norm_num : (5 / 4 : ℝ) ≤ 2))
    simpa using! hh
  have h := positiveCount_backlund_integral_bound hT hr
  exact h.trans_le (add_le_add
    (add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_right hp Real.pi_pos.le)) le_rfl) le_rfl)

#print axioms norm_logDeriv_zeta_le_real_negative_part
#print axioms zeta_real_log_norm_hasDerivAt
#print axioms backlundLog_right_reference
#print axioms norm_backlundLog_le_real_log_zeta
#print axioms positiveCount_backlund_real_log_bound

end LiuWang.Proof.Campaign20260915.RosserCount
