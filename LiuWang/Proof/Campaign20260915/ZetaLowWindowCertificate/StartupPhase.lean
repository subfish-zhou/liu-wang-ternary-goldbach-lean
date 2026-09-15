import LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate.LowHeightRemainder
import LiuWang.Proof.Campaign20260915.ZetaValidation.StirlingRational

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

open LiuWang.Proof.Campaign20260915.ZetaValidation

def startupArgumentCenter (t : ℚ) : ℚ :=
  t / 4 * dyadicLog (1 / 16 + t ^ 2 / 4) 26 24 -
    (1 / 4) * (rationalPi20 / 2 - rationalAtanTaylor 8 (1 / (2 * t))) -
      t / 2 - t / 2 * dyadicLog rationalPi20 2 24

noncomputable section

theorem startupArgumentCenter_error {t : ℚ} (htlo : 12570 ≤ t) (hthi : t ≤ 12580) :
    |criticalGammaArgument (t : ℝ) - (startupArgumentCenter t : ℝ)| ≤ 1 / 10 := by
  have htpos : (0 : ℚ) < t := by linarith
  have htRlo : (12570 : ℝ) ≤ t := by exact_mod_cast htlo
  have htRhi : (t : ℝ) ≤ 12580 := by exact_mod_cast hthi
  have htRpos : (0 : ℝ) < t := by linarith
  have hsqlo := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 12570) htlo 2
  have hsqhi := pow_le_pow_left₀ htpos.le hthi 2
  have hlog := dyadicLog_error (q := 1 / 16 + t ^ 2 / 4) (k := 26)
    (by norm_num; linarith) (by norm_num; linarith) 24
  have hpi := dyadicLog_error (q := rationalPi20) (k := 2)
    (by norm_num [rationalPi20]) (by norm_num [rationalPi20]) 24
  have hatan := rationalAtanTaylor_error 8 (q := 1 / (2 * t)) (by
    rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    linarith)
  have hpie := rationalPi20_error
  have hpilog := log_rationalPi20_error
  have hlogpi := abs_sub_le (Real.log Real.pi) (Real.log (rationalPi20 : ℝ))
    (dyadicLog rationalPi20 2 24 : ℝ)
  have hlogpib :
      |Real.log Real.pi - (dyadicLog rationalPi20 2 24 : ℝ)| ≤ 1 / 1000000 := by
    norm_num at hpi
    linarith
  have hlogb : |Real.log (1 / 16 + (t : ℝ) ^ 2 / 4) -
      (dyadicLog (1 / 16 + t ^ 2 / 4) 26 24 : ℝ)| ≤ 1 / 100000 := by
    push_cast at hlog
    norm_num at hlog
    linarith
  have hm1 : |(t : ℝ) / 4 * (Real.log (1 / 16 + (t : ℝ) ^ 2 / 4) -
      (dyadicLog (1 / 16 + t ^ 2 / 4) 26 24 : ℝ))| ≤ 12580 / 400000 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < (t : ℝ) / 4)]
    exact (mul_le_mul_of_nonneg_left hlogb (by positivity)).trans (by linarith)
  have hm2 : |(t : ℝ) / 2 * (Real.log Real.pi -
      (dyadicLog rationalPi20 2 24 : ℝ))| ≤ 12580 / 2000000 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < (t : ℝ) / 2)]
    exact (mul_le_mul_of_nonneg_left hlogpib (by positivity)).trans (by linarith)
  have hmain : |criticalGammaStirlingArgument (t : ℝ) -
      (startupArgumentCenter t : ℝ)| ≤ 1 / 20 := by
    rw [criticalGammaStirlingArgument_elementary htRpos]
    unfold startupArgumentCenter
    push_cast
    push_cast at hatan
    rw [abs_le] at hm1 hm2 hatan hpie ⊢
    constructor <;> linarith [hm1.1, hm1.2, hm2.1, hm2.2, hatan.1, hatan.2,
      hpie.1, hpie.2]
  have hst := criticalGammaStirlingArgument_error htRpos
  have hstb : 1 / (4 * (t : ℝ)) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hsum := abs_sub_le (criticalGammaArgument (t : ℝ))
    (criticalGammaStirlingArgument (t : ℝ)) (startupArgumentCenter t : ℝ)
  linarith

theorem startup_left_rational :
    startupArgumentCenter 12570 + 1 / 10 < 13210 * rationalPi20 := by
  norm_num [startupArgumentCenter, dyadicLog, logOneMinusSeries, rationalPi20,
    rationalAtanTaylor, imagIPower, Finset.sum_range_succ]

theorem startup_right_rational :
    13210 * (rationalPi20 + 1 / 100000000000000000000) <
      startupArgumentCenter 12580 - 1 / 10 := by
  norm_num [startupArgumentCenter, dyadicLog, logOneMinusSeries, rationalPi20,
    rationalAtanTaylor, imagIPower, Finset.sum_range_succ]

theorem startup_left_argument :
    criticalGammaArgument 12570 < 13210 * Real.pi := by
  have he := (abs_le.mp (startupArgumentCenter_error
    (t := 12570) (by norm_num) (by norm_num))).2
  have hq : ((startupArgumentCenter 12570 + 1 / 10 : ℚ) : ℝ) <
      ((13210 * rationalPi20 : ℚ) : ℝ) := Rat.cast_lt.mpr startup_left_rational
  push_cast at hq
  have hp := Real.pi_gt_d20
  norm_num [rationalPi20] at hq
  norm_num only [Rat.cast_ofNat] at he
  linarith

theorem startup_right_argument :
    13210 * Real.pi < criticalGammaArgument 12580 := by
  have he := (abs_le.mp (startupArgumentCenter_error
    (t := 12580) (by norm_num) (by norm_num))).1
  have hq : ((13210 * (rationalPi20 + 1 / 100000000000000000000) : ℚ) : ℝ) <
      ((startupArgumentCenter 12580 - 1 / 10 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr startup_right_rational
  push_cast at hq
  have hp := (abs_le.mp rationalPi20_error).2
  norm_num only [Rat.cast_ofNat] at he
  linarith

#print axioms startupArgumentCenter_error
#print axioms startup_left_rational
#print axioms startup_right_rational
#print axioms startup_left_argument
#print axioms startup_right_argument

end
end LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate
