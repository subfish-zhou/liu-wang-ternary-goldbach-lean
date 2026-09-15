import LiuWang.Proof.Campaign20260915.ZetaValidation.GammaStirlingPhase
import LiuWang.Proof.Campaign20260915.ZetaValidation.DyadicLogarithm

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rationalPi20 : ℚ := 314159265358979323846 / 100000000000000000000

def originalHeightGammaArgumentCenter : ℚ :=
  1894438 / 4 * dyadicLog (1 / 16 + 1894438 ^ 2 / 4) 40 80 -
    (1 / 4) * (rationalPi20 / 2 - rationalAtanTaylor 80 (1 / (2 * 1894438))) -
      1894438 / 2 - 1894438 / 2 * dyadicLog rationalPi20 2 80

noncomputable section

open Complex

theorem gammaStirlingPhase_elementary {z : ℂ} (hz : 0 < z.re) (ht : 0 < z.im) :
    gammaStirlingPhase z =
      z.im / 2 * Real.log (normSq z) +
        (z.re - 1 / 2) * (Real.pi / 2 - Real.arctan (z.re / z.im)) - z.im := by
  have ha : (log z).im = Real.pi / 2 - Real.arctan (z.re / z.im) := by
    rw [log_im_of_re_pos hz,
      show z.im / z.re = (z.re / z.im)⁻¹ by rw [inv_div],
      Real.arctan_inv_of_pos (by positivity)]
  rw [gammaStirlingPhase, sub_im, mul_im, sub_re, sub_im, ha, log_re,
    Complex.norm_def, Real.log_sqrt (normSq_nonneg z)]
  norm_num
  ring

theorem criticalGammaStirlingArgument_elementary {t : ℝ} (ht : 0 < t) :
    criticalGammaStirlingArgument t =
      t / 4 * Real.log (1 / 16 + t ^ 2 / 4) -
        (1 / 4) * (Real.pi / 2 - Real.arctan (1 / (2 * t))) -
          t / 2 - t / 2 * Real.log Real.pi := by
  rw [criticalGammaStirlingArgument, gammaStirlingPhase_elementary
    (by norm_num [criticalPoint] : 0 < (criticalPoint t / 2).re)
    (by simpa [criticalPoint] using ht : 0 < (criticalPoint t / 2).im)]
  simp [criticalPoint, normSq_apply]
  ring_nf

theorem rationalPi20_error :
    |Real.pi - (rationalPi20 : ℝ)| ≤ 1 / 100000000000000000000 := by
  have hl := Real.pi_gt_d20
  have hu := Real.pi_lt_d20
  rw [abs_le]
  norm_num [rationalPi20] at *
  constructor <;> linarith

theorem log_rationalPi20_error :
    |Real.log Real.pi - Real.log (rationalPi20 : ℝ)| ≤ 1 / 100000000000000000000 := by
  have hp : (0 : ℝ) < rationalPi20 := by norm_num [rationalPi20]
  have hl : (rationalPi20 : ℝ) ≤ Real.pi := by
    norm_num [rationalPi20]
    linarith [Real.pi_gt_d20]
  have hlo := Real.log_le_log hp hl
  have hhi := Real.log_le_sub_one_of_pos (show 0 < Real.pi / (rationalPi20 : ℝ) by positivity)
  rw [Real.log_div Real.pi_pos.ne' hp.ne'] at hhi
  have he := (abs_le.mp rationalPi20_error).2
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hratio : Real.pi / (rationalPi20 : ℝ) - 1 ≤ 1 / 100000000000000000000 := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hp).mpr
    norm_num [rationalPi20] at he ⊢
    linarith
  exact hhi.trans hratio

theorem originalHeightGammaArgumentCenter_error :
    |criticalGammaArgument 1894438 - (originalHeightGammaArgumentCenter : ℝ)| ≤
      1 / 1000000 := by
  have hst := criticalGammaStirlingArgument_error (t := 1894438) (by norm_num)
  have hlog := dyadicLog_error (q := 1 / 16 + 1894438 ^ 2 / 4) (k := 40)
    (by norm_num) (by norm_num) 80
  have hpi := dyadicLog_error (q := rationalPi20) (k := 2)
    (by norm_num [rationalPi20]) (by norm_num [rationalPi20]) 80
  have hatan := rationalAtanTaylor_error 80 (q := 1 / (2 * 1894438)) (by norm_num)
  have hpie := rationalPi20_error
  have hpilog := log_rationalPi20_error
  have hsum := abs_sub_le (Real.log Real.pi) (Real.log (rationalPi20 : ℝ))
    (dyadicLog rationalPi20 2 80 : ℝ)
  have hmain : |criticalGammaStirlingArgument 1894438 -
      (originalHeightGammaArgumentCenter : ℝ)| ≤ 1 / 1000000000000 := by
    rw [criticalGammaStirlingArgument_elementary (by norm_num)]
    unfold originalHeightGammaArgumentCenter
    push_cast
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
      Nat.cast_ofNat] at hlog hatan hpi
    rw [abs_le] at hlog hatan hpie hpilog hpi ⊢
    constructor <;> linarith [hlog.1, hlog.2, hatan.1, hatan.2, hpie.1, hpie.2,
      hpilog.1, hpilog.2, hpi.1, hpi.2]
  have h := abs_sub_le (criticalGammaArgument 1894438)
    (criticalGammaStirlingArgument 1894438) (originalHeightGammaArgumentCenter : ℝ)
  norm_num at hst
  linarith

theorem originalHeightGammaPhase_rational_argument_error :
    ‖criticalGammaPhase 1894438 -
      Complex.exp (((originalHeightGammaArgumentCenter : ℝ) : ℂ) * I)‖ ≤ 1 / 1000000 := by
  rw [criticalGammaPhase_eq_exp_argument]
  exact (unitPhase_distance_le _ _).trans originalHeightGammaArgumentCenter_error

#print axioms criticalGammaStirlingArgument_elementary
#print axioms originalHeightGammaArgumentCenter_error
#print axioms originalHeightGammaPhase_rational_argument_error

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
