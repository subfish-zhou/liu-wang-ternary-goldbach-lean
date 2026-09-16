import LiuWang.Proof.Campaign20260915.RosserCount.GammaPhaseError
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightPhase
import LiuWang.Proof.DirichletZeroCount.Remainder.SourceGamma

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open LiuWang.Proof.DirichletZeroCount.Remainder
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RosserCount

private theorem arctan_le_self_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.arctan x ≤ x := by
  have hden (u : ℝ) : (1 + u ^ 2) ≠ 0 := by positivity
  have hc : Continuous (fun u : ℝ => 1 / (1 + u ^ 2)) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u (_ : u ∈ Set.uIcc (0 : ℝ) x) => Real.hasDerivAt_arctan u)
    (hc.intervalIntegrable 0 x)
  have hb := intervalIntegral.integral_mono_on (μ := volume) hx (hc.intervalIntegrable 0 x)
    (intervalIntegrable_const (c := (1 : ℝ))) (fun u _ =>
      (div_le_one (by positivity : 0 < 1 + u ^ 2)).mpr (by nlinarith [sq_nonneg u]))
  simpa only [hi, Real.arctan_zero, sub_zero, intervalIntegral.integral_const,
    smul_eq_mul, mul_one] using hb

theorem rosser_stirling_correction_bounds {T : ℝ} (hT : 0 < T) :
    0 ≤ stirlingPhase (criticalPoint T / 2) -
        T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8 ∧
      stirlingPhase (criticalPoint T / 2) -
        T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8 ≤ 3 / (16 * T) := by
  let z := criticalPoint T / 2
  have hzre : z.re = 1 / 4 := by norm_num [z, criticalPoint]
  have hzim : z.im = T / 2 := by simp [z, criticalPoint]
  have hns : normSq z = 1 / 16 + T ^ 2 / 4 := by
    rw [normSq_apply, hzre, hzim]
    ring
  have hnorm : ‖z‖ ^ 2 = (T / 2) ^ 2 * (1 + 1 / (4 * T ^ 2)) := by
    rw [← normSq_eq_norm_sq, hns]
    field_simp
    ring
  have hl :
      Real.log ‖z‖ - Real.log (T / 2) =
        Real.log (1 + 1 / (4 * T ^ 2)) / 2 := by
    have h := congrArg Real.log hnorm
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
    linarith
  have hl0 : 0 ≤ Real.log ‖z‖ - Real.log (T / 2) := by
    rw [hl]
    exact div_nonneg (Real.log_nonneg
      (by linarith [show (0 : ℝ) ≤ 1 / (4 * T ^ 2) by positivity])) (by norm_num)
  have hlu :
      Real.log ‖z‖ - Real.log (T / 2) ≤ 1 / (8 * T ^ 2) := by
    rw [hl]
    have h := Real.log_le_sub_one_of_pos
      (by positivity : 0 < 1 + 1 / (4 * T ^ 2))
    have he : 1 / (4 * T ^ 2) / 2 = 1 / (8 * T ^ 2) := by ring
    rw [← he]
    linarith
  have harg : z.arg = Real.arctan (2 * T) := by
    rw [arg_eq_arctan_of_re_pos (by rw [hzre]; norm_num), hzre, hzim]
    congr 1
    ring
  have hc : Real.pi / 2 - z.arg = Real.arctan ((2 * T)⁻¹) := by
    rw [harg, Real.arctan_inv_of_pos (by positivity : 0 < 2 * T)]
  have ha0 : 0 ≤ Real.pi / 2 - z.arg := by
    rw [hc]
    exact Real.arctan_nonneg.mpr (by positivity)
  have hau : Real.pi / 2 - z.arg ≤ 1 / (2 * T) := by
    rw [hc, one_div]
    exact arctan_le_self_nonneg (by positivity)
  have he :
      stirlingPhase z - T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8 =
        T / 2 * (Real.log ‖z‖ - Real.log (T / 2)) + (Real.pi / 2 - z.arg) / 4 := by
    simp only [stirlingPhase, sub_im, mul_im, sub_re, div_ofNat_re, div_ofNat_im,
      one_re, one_im, log_re, log_im, hzre, hzim]
    ring
  change 0 ≤ _ ∧ _ ≤ _
  rw [he]
  constructor
  · positivity
  · have hb := mul_le_mul_of_nonneg_left hlu (by positivity : 0 ≤ T / 2)
    have hd := div_le_div_of_nonneg_right hau (by norm_num : (0 : ℝ) ≤ 4)
    have hs : T / 2 * (1 / (8 * T ^ 2)) + (1 / (2 * T)) / 4 = 3 / (16 * T) := by
      field_simp
      ring
    rw [← hs]
    linarith

theorem abs_rosserGammaRemainder_lt_quarter_inv {T : ℝ} (hT : 0 < T) :
    |rosserGammaRemainder T| < 1 / (4 * T) := by
  let z := criticalPoint T / 2
  have hzre : z.re = 1 / 4 := by norm_num [z, criticalPoint]
  have hzim : z.im = T / 2 := by simp [z, criticalPoint]
  have hz : 0 < z.re := by rw [hzre]; norm_num
  have hy : 0 ≤ z.im := by rw [hzim]; positivity
  have hns : normSq z = 1 / 16 + T ^ 2 / 4 := by
    rw [normSq_apply, hzre, hzim]
    ring
  have hb : z.im / (8 * normSq z) < 1 / (4 * T) := by
    rw [hzim, hns]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hg := abs_le.mp (logGamma_stirling_im_error hz hy)
  have hgu := logGamma_im_le_stirling hz hy
  have hd := rosser_stirling_correction_bounds hT
  have he :
      rosserGammaRemainder T =
        ((logGamma z).im - stirlingPhase z) +
          (stirlingPhase z - T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8) := by
    simp only [rosserGammaRemainder, gammaLogBranch, logGamma, z]
    ring
  have hc : 3 / (16 * T) < 1 / (4 * T) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  rw [he, abs_lt]
  constructor <;> linarith

theorem positiveCount_backlund_gamma_paid_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi +
      4 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  have hT0 : 0 < T := by linarith [rsA_ge_thousand]
  have hg := div_le_div_of_nonneg_right
    (abs_rosserGammaRemainder_lt_quarter_inv hT0).le Real.pi_pos.le
  have he : (1 / (4 * T)) / Real.pi = 1 / (4 * Real.pi * T) := by ring
  rw [he] at hg
  exact (positiveCount_backlund_real_log_bound hT hr).trans_le (add_le_add le_rfl hg)

#print axioms rosser_stirling_correction_bounds
#print axioms abs_rosserGammaRemainder_lt_quarter_inv
#print axioms positiveCount_backlund_gamma_paid_bound

end LiuWang.Proof.Campaign20260915.RosserCount
