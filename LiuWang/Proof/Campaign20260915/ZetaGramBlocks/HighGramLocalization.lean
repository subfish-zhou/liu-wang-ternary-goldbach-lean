import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.GramSequence
import LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate.StartupWindow

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaGramBlocks

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

def highArgumentCenter (t : ℚ) (k : ℕ) : ℚ :=
  t / 4 * dyadicLog (1 / 16 + t ^ 2 / 4) k 48 -
    (1 / 4) * (rationalPi20 / 2 - rationalAtanTaylor 24 (1 / (2 * t))) -
      t / 2 - t / 2 * dyadicLog rationalPi20 2 48

noncomputable section

theorem startupHeight_eq_gramPoint : startupHeight = gramPoint 13210 :=
  criticalGammaArgument_strictMono.injOn
    (show startupHeight ∈ Set.Ici 16 from by
      change 16 ≤ startupHeight
      linarith [startupHeight_bounds.1]) (gramPoint_gt_sixteen _).le
    (startupHeight_isGramPoint.trans (gramPoint_phase 13210).symm)

theorem gramPoint_after_startup {n : ℕ} (hn : 13210 < n) :
    startupHeight < gramPoint n := by
  rw [startupHeight_eq_gramPoint]
  exact gramPoint_strictMono hn

theorem highArgumentCenter_error {t : ℚ} {k : ℕ}
    (htlo : 12570 ≤ t) (hthi : t ≤ 1894440) (hk : k ≤ 40)
    (hlo : 1 / 2 ≤ (1 / 16 + t ^ 2 / 4) / 2 ^ k)
    (hhi : (1 / 16 + t ^ 2 / 4) / 2 ^ k ≤ 1) :
    |criticalGammaArgument (t : ℝ) - (highArgumentCenter t k : ℝ)| ≤ 1 / 40000 := by
  have htpos : (0 : ℚ) < t := by linarith
  have htRlo : (12570 : ℝ) ≤ t := by exact_mod_cast htlo
  have htRhi : (t : ℝ) ≤ 1894440 := by exact_mod_cast hthi
  have htRpos : (0 : ℝ) < t := by linarith
  have hkR : (k : ℝ) ≤ 40 := by exact_mod_cast hk
  have hlog := dyadicLog_error hlo hhi 48
  have hpi := dyadicLog_error (q := rationalPi20) (k := 2)
    (by norm_num [rationalPi20]) (by norm_num [rationalPi20]) 48
  have hatan := rationalAtanTaylor_error 24 (q := 1 / (2 * t)) (by
    rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    linarith)
  have hpie := rationalPi20_error
  have hpilog := log_rationalPi20_error
  have hlogpi := abs_sub_le (Real.log Real.pi) (Real.log (rationalPi20 : ℝ))
    (dyadicLog rationalPi20 2 48 : ℝ)
  have hlogpib :
      |Real.log Real.pi - (dyadicLog rationalPi20 2 48 : ℝ)| ≤ 1 / 10 ^ 13 := by
    norm_num at hpi
    linarith
  have hlogb : |Real.log (1 / 16 + (t : ℝ) ^ 2 / 4) -
      (dyadicLog (1 / 16 + t ^ 2 / 4) k 48 : ℝ)| ≤ 1 / 10 ^ 12 := by
    push_cast at hlog
    norm_num at hlog
    linarith
  have hm1 : |(t : ℝ) / 4 * (Real.log (1 / 16 + (t : ℝ) ^ 2 / 4) -
      (dyadicLog (1 / 16 + t ^ 2 / 4) k 48 : ℝ))| ≤ 1894440 / (4 * 10 ^ 12) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < (t : ℝ) / 4)]
    exact (mul_le_mul_of_nonneg_left hlogb (by positivity)).trans (by linarith)
  have hm2 : |(t : ℝ) / 2 * (Real.log Real.pi -
      (dyadicLog rationalPi20 2 48 : ℝ))| ≤ 1894440 / (2 * 10 ^ 13) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < (t : ℝ) / 2)]
    exact (mul_le_mul_of_nonneg_left hlogpib (by positivity)).trans (by linarith)
  have hmain : |criticalGammaStirlingArgument (t : ℝ) -
      (highArgumentCenter t k : ℝ)| ≤ 1 / 1000000 := by
    rw [criticalGammaStirlingArgument_elementary htRpos]
    unfold highArgumentCenter
    push_cast
    push_cast at hatan
    rw [abs_le] at hm1 hm2 hatan hpie ⊢
    constructor <;> linarith [hm1.1, hm1.2, hm2.1, hm2.2, hatan.1, hatan.2,
      hpie.1, hpie.2]
  have hst := criticalGammaStirlingArgument_error htRpos
  have hstb : 1 / (4 * (t : ℝ)) ≤ 1 / 50280 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hsum := abs_sub_le (criticalGammaArgument (t : ℝ))
    (criticalGammaStirlingArgument (t : ℝ)) (highArgumentCenter t k : ℝ)
  linarith

theorem gramPoint_localized_by_rational_phase {n k : ℕ} {a b : ℚ}
    (ha : 12570 ≤ a) (hb : b ≤ 1894440) (hab : a < b) (hk : k ≤ 40)
    (hal : 1 / 2 ≤ (1 / 16 + a ^ 2 / 4) / 2 ^ k)
    (hau : (1 / 16 + a ^ 2 / 4) / 2 ^ k ≤ 1)
    (hbl : 1 / 2 ≤ (1 / 16 + b ^ 2 / 4) / 2 ^ k)
    (hbu : (1 / 16 + b ^ 2 / 4) / 2 ^ k ≤ 1)
    (hleft : highArgumentCenter a k + 1 / 40000 < n * rationalPi20)
    (hright : n * (rationalPi20 + 1 / 10 ^ 20) <
      highArgumentCenter b k - 1 / 40000) :
    gramPoint n ∈ Set.Ioo (a : ℝ) (b : ℝ) := by
  have hea := (abs_le.mp (highArgumentCenter_error ha (hab.le.trans hb) hk hal hau)).2
  have heb := (abs_le.mp (highArgumentCenter_error (ha.trans hab.le) hb hk hbl hbu)).1
  have hl := Rat.cast_lt (K := ℝ).mpr hleft
  have hr := Rat.cast_lt (K := ℝ).mpr hright
  have hpi := (abs_le.mp rationalPi20_error).2
  have hpilo : (rationalPi20 : ℝ) ≤ Real.pi := by
    norm_num [rationalPi20]
    linarith [Real.pi_gt_d20]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  push_cast at hl hr
  apply gramPoint_mem_of_phase_bracket
    (by
      have h : (12570 : ℝ) ≤ a := by exact_mod_cast ha
      linarith)
    (by exact_mod_cast hab)
  · nlinarith [mul_le_mul_of_nonneg_left hpilo hn]
  · nlinarith [mul_le_mul_of_nonneg_left hpi hn]

end
end LiuWang.Proof.Campaign20260915.ZetaGramBlocks
