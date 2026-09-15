import LiuWang.Proof.Campaign20260915.ZetaValidation.HighOrderUniform
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

open LiuWang.Proof.Campaign20260915.ZetaValidation

def lowPrefix (t : ℝ) : ℕ :=
  if |t| ≤ 900 then 2048
  else if |t| ≤ 1900 then 4096
  else if |t| ≤ 4000 then 8192
  else if |t| ≤ 8100 then 16384
  else 32768

theorem lowPrefix_bounds (t : ℝ) :
    1 ≤ lowPrefix t ∧ lowPrefix t ≤ 32768 := by
  unfold lowPrefix
  split_ifs <;> norm_num

theorem lowPrefix_scale {s : ℂ}
    (hslo : 1 / 2 ≤ s.re) (hshi : s.re ≤ 2) (ht : |s.im| ≤ 12600) :
    ‖s‖ + (63 : ℝ) ≤ (lowPrefix s.im : ℝ) / 2 := by
  have hn := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at hn
  unfold lowPrefix
  split_ifs <;> push_cast <;> linarith

theorem bounded_prefix_order64_remainder {s : ℂ}
    (hslo : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) {N : ℕ}
    (hN : 1 ≤ N) (hNhi : N ≤ 32768)
    (hscale : ‖s‖ + (63 : ℝ) ≤ (N : ℝ) / 2) :
    ‖riemannZeta s - eulerMaclaurinApprox s N 63‖ ≤
      1 / 1000000000000000000 := by
  have he := eulerMaclaurin_geometric_error 63
    (by linarith : 1 / 10 < s.re) hs1 hN hscale
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNu : (N : ℝ) ≤ 65536 := by
    have h : (N : ℝ) ≤ 32768 := by exact_mod_cast hNhi
    linarith
  have hp : (N : ℝ) ^ (1 - s.re) ≤ 256 := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ ≤ (65536 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hNu (by norm_num)
      _ = _ := by rw [← Real.sqrt_eq_rpow]; norm_num
  have hd : (2 : ℝ) ^ (63 + 2) * (1 / 2 + 63) ≤
      (2 : ℝ) ^ (63 + 2) * (s.re + 63) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpos : 0 < (2 : ℝ) ^ (63 + 2) * (s.re + 63) := by positivity
  calc
    _ ≤ (N : ℝ) ^ (1 - s.re) /
        ((2 : ℝ) ^ (63 + 2) * (s.re + 63)) := he
    _ ≤ 256 / ((2 : ℝ) ^ (63 + 2) * (s.re + 63)) :=
      div_le_div_of_nonneg_right hp hpos.le
    _ ≤ 256 / ((2 : ℝ) ^ (63 + 2) * (1 / 2 + 63)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
    _ ≤ _ := by norm_num

theorem low_order64_remainder {s : ℂ}
    (hslo : 1 / 2 ≤ s.re) (hshi : s.re ≤ 2)
    (ht : |s.im| ≤ 12600) (hs1 : s ≠ 1) :
    ‖riemannZeta s - eulerMaclaurinApprox s (lowPrefix s.im) 63‖ ≤
      1 / 1000000000000000000 :=
  bounded_prefix_order64_remainder hslo hs1
    (lowPrefix_bounds s.im).1 (lowPrefix_bounds s.im).2
    (lowPrefix_scale hslo hshi ht)

theorem low_critical_order64_remainder {t : ℝ} (ht : |t| ≤ 12600) :
    ‖riemannZeta (criticalPoint t) -
      eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63‖ ≤
        1 / 1000000000000000000 :=
  low_order64_remainder (by norm_num [criticalPoint]) (by norm_num [criticalPoint])
    ht (criticalPoint_ne_one t)

theorem low_normalized_order64_remainder {t : ℝ} (ht : |t| ≤ 12600) :
    |normalizedCriticalZeta t -
      (eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63 *
        criticalGammaPhase t).re| ≤ 1 / 1000000000000000000 := by
  have he : normalizedCriticalZeta t -
      (eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63 *
        criticalGammaPhase t).re =
      ((riemannZeta (criticalPoint t) -
        eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63) *
        criticalGammaPhase t).re := by
    rw [sub_mul, sub_re, ← normalizedCriticalZeta_ofReal, ofReal_re]
  rw [he]
  have h := abs_re_le_norm
    ((riemannZeta (criticalPoint t) -
      eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63) * criticalGammaPhase t)
  rw [norm_mul, norm_criticalGammaPhase, mul_one] at h
  exact h.trans (low_critical_order64_remainder ht)

theorem source_thresholds_below_start :
    (168 : ℝ) * Real.pi < 12570 ∧
      (250 : ℝ) * Real.pi < 12570 ∧ (4000 : ℝ) * Real.pi < 12570 := by
  have hp := Real.pi_lt_d20
  constructor
  · linarith
  constructor <;> linarith

theorem low_source_window_covered {t : ℝ}
    (htlo : 16 < t) (hthi : t ≤ 4000 * Real.pi) :
    |t| ≤ 12600 := by
  rw [abs_of_pos (by linarith : 0 < t)]
  linarith [source_thresholds_below_start.2.2]

#print axioms low_order64_remainder
#print axioms low_normalized_order64_remainder
#print axioms source_thresholds_below_start

end LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate
