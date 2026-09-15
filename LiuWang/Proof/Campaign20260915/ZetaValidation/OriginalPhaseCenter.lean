import LiuWang.Proof.Campaign20260915.ZetaValidation.PrecisionPhase
import LiuWang.Proof.Campaign20260915.ZetaValidation.StirlingRational

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def originalHeightRoundedArgument : ℚ :=
  roundRationalAt (10 ^ 24) originalHeightGammaArgumentCenter

def originalHeightGammaPhaseCenter : QComplex :=
  unitPhaseAt (10 ^ 40) 40 32 (originalHeightRoundedArgument / 2 ^ 32)

noncomputable section
open Complex

theorem originalHeightGammaArgumentCenter_abs :
    |(originalHeightGammaArgumentCenter : ℝ)| ≤ 100000000 := by
  have hlog := dyadicLog_error (q := 1 / 16 + 1894438 ^ 2 / 4) (k := 40)
    (by norm_num) (by norm_num) 80
  have hpi := dyadicLog_error (q := rationalPi20) (k := 2)
    (by norm_num [rationalPi20]) (by norm_num [rationalPi20]) 80
  have hatan := rationalAtanTaylor_error 80 (q := 1 / (2 * 1894438)) (by norm_num)
  have hl0 : 0 ≤ Real.log (1 / 16 + (1894438 : ℝ) ^ 2 / 4) := Real.log_nonneg (by norm_num)
  have hl40 : Real.log (1 / 16 + (1894438 : ℝ) ^ 2 / 4) ≤ 40 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ 40) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 40 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 40 := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        norm_num at h
        linarith
  have hp0 : 0 ≤ Real.log (rationalPi20 : ℝ) := Real.log_nonneg (by norm_num [rationalPi20])
  have hp4 : Real.log (rationalPi20 : ℝ) ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < rationalPi20 by norm_num [rationalPi20])
    norm_num [rationalPi20] at h ⊢
    linarith
  have ha0 : 0 ≤ Real.arctan (1 / (2 * (1894438 : ℝ))) := Real.arctan_nonneg.mpr (by positivity)
  have ha2 : Real.arctan (1 / (2 * (1894438 : ℝ))) ≤ 2 := by
    have h := Real.arctan_lt_pi_div_two (1 / (2 * (1894438 : ℝ)))
    linarith [Real.pi_lt_four]
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Nat.cast_ofNat] at hlog hpi hatan
  unfold originalHeightGammaArgumentCenter
  push_cast
  rw [abs_le] at hlog hpi hatan ⊢
  norm_num only [rationalPi20, Rat.cast_div, Rat.cast_ofNat] at *
  constructor <;> linarith [hlog.1, hlog.2, hpi.1, hpi.2, hatan.1, hatan.2]

theorem originalHeightRoundedArgument_error :
    |(originalHeightRoundedArgument : ℝ) - (originalHeightGammaArgumentCenter : ℝ)| ≤
      1 / (10 : ℝ) ^ 24 := by
  have h := roundRationalAt_error (D := 10 ^ 24) (by norm_num) originalHeightGammaArgumentCenter
  unfold originalHeightRoundedArgument
  norm_num at h ⊢
  exact h

theorem originalHeightRoundedArgument_reduced :
    |originalHeightRoundedArgument / 2 ^ 32| ≤ (1 : ℚ) := by
  have h := abs_add_le ((originalHeightRoundedArgument : ℝ) -
    (originalHeightGammaArgumentCenter : ℝ)) (originalHeightGammaArgumentCenter : ℝ)
  rw [sub_add_cancel] at h
  have hb : |(originalHeightRoundedArgument : ℝ)| ≤ 2 ^ 32 := by
    linarith [originalHeightRoundedArgument_error, originalHeightGammaArgumentCenter_abs]
  have hq : |originalHeightRoundedArgument| ≤ (2 : ℚ) ^ 32 := by exact_mod_cast hb
  rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ 32),
    div_le_one (by positivity)]
  exact hq

theorem originalHeightGammaPhaseCenter_error :
    ‖criticalGammaPhase 1894438 - originalHeightGammaPhaseCenter.toComplex‖ ≤
      1 / 1000000 + 2 / (10 : ℝ) ^ 24 := by
  have hs := unitPhaseAt_original_scale originalHeightRoundedArgument_reduced (k := 32) le_rfl
  have hid : (2 : ℝ) ^ 32 * ((originalHeightRoundedArgument / 2 ^ 32 : ℚ) : ℝ) =
      (originalHeightRoundedArgument : ℝ) := by push_cast; ring
  rw [hid] at hs
  have ha := unitPhase_distance_le (originalHeightGammaArgumentCenter : ℝ)
    (originalHeightRoundedArgument : ℝ)
  have hr := originalHeightRoundedArgument_error
  rw [abs_sub_comm] at hr
  have hp := norm_sub_le_norm_sub_add_norm_sub (criticalGammaPhase 1894438)
    (exp (((originalHeightGammaArgumentCenter : ℝ) : ℂ) * I))
    (exp (((originalHeightRoundedArgument : ℝ) : ℂ) * I))
  have hf := norm_sub_le_norm_sub_add_norm_sub (criticalGammaPhase 1894438)
    (exp (((originalHeightRoundedArgument : ℝ) : ℂ) * I))
    originalHeightGammaPhaseCenter.toComplex
  change ‖exp (((originalHeightRoundedArgument : ℝ) : ℂ) * I) -
    originalHeightGammaPhaseCenter.toComplex‖ ≤ _ at hs
  linarith [originalHeightGammaPhase_rational_argument_error]

#print axioms originalHeightGammaPhaseCenter_error

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
