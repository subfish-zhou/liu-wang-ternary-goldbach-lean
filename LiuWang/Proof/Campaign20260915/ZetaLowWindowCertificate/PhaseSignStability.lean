import LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate.StartupPhase
import LiuWang.Proof.Campaign20260915.ZetaWinding.LocalLog

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

open LiuWang.Proof.Campaign20260915.ZetaValidation

def rotationFactor (t : ℝ) (p : ℂ) : ℝ := (p / criticalGammaPhase t).re

theorem rotated_critical_re (t : ℝ) (p : ℂ) :
    (riemannZeta (criticalPoint t) * p).re =
      normalizedCriticalZeta t * rotationFactor t p := by
  have hp : criticalGammaPhase t ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_criticalGammaPhase]
    norm_num
  have he : riemannZeta (criticalPoint t) * p =
      (normalizedCriticalZeta t : ℂ) * (p / criticalGammaPhase t) := by
    rw [normalizedCriticalZeta_ofReal]
    field_simp
  rw [he, mul_re]
  simp [rotationFactor]

theorem rotationFactor_error {t δ : ℝ} {p : ℂ}
    (he : ‖p - criticalGammaPhase t‖ ≤ δ) :
    |rotationFactor t p - 1| ≤ δ := by
  have hp : criticalGammaPhase t ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_criticalGammaPhase]
    norm_num
  have hid : p / criticalGammaPhase t - 1 =
      (p - criticalGammaPhase t) / criticalGammaPhase t := by
    field_simp
  have hn : ‖p / criticalGammaPhase t - 1‖ ≤ δ := by
    rw [hid, norm_div, norm_criticalGammaPhase, div_one]
    exact he
  simpa only [rotationFactor, sub_re, one_re] using
    (abs_re_le_norm (p / criticalGammaPhase t - 1)).trans hn

theorem rotationFactor_pos {t δ : ℝ} {p : ℂ}
    (he : ‖p - criticalGammaPhase t‖ ≤ δ) (hδ : δ < 1) :
    0 < rotationFactor t p := by
  have h := (abs_le.mp (rotationFactor_error he)).1
  linarith

theorem rotated_critical_pos_iff {t δ : ℝ} {p : ℂ}
    (he : ‖p - criticalGammaPhase t‖ ≤ δ) (hδ : δ < 1) :
    0 < (riemannZeta (criticalPoint t) * p).re ↔ 0 < normalizedCriticalZeta t := by
  rw [rotated_critical_re]
  exact mul_pos_iff_of_pos_right (rotationFactor_pos he hδ)

theorem rotated_critical_neg_iff {t δ : ℝ} {p : ℂ}
    (he : ‖p - criticalGammaPhase t‖ ≤ δ) (hδ : δ < 1) :
    (riemannZeta (criticalPoint t) * p).re < 0 ↔ normalizedCriticalZeta t < 0 := by
  rw [rotated_critical_re]
  have hp := rotationFactor_pos he hδ
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg (not_lt.mp hn) hp.le)) h
  · intro h
    exact mul_neg_of_neg_of_pos h hp

theorem low_rotated_em_error {t : ℝ} (ht : |t| ≤ 12600) (p : ℂ) :
    |(riemannZeta (criticalPoint t) * p).re -
      (eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63 * p).re| ≤
        ‖p‖ / 1000000000000000000 := by
  have he : (riemannZeta (criticalPoint t) * p).re -
      (eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63 * p).re =
      ((riemannZeta (criticalPoint t) -
        eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63) * p).re := by
    rw [sub_mul, sub_re]
  rw [he]
  have h := abs_re_le_norm ((riemannZeta (criticalPoint t) -
    eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63) * p)
  rw [norm_mul] at h
  exact h.trans ((mul_le_mul_of_nonneg_right
    (low_critical_order64_remainder ht) (norm_nonneg p)).trans_eq (by ring))

theorem low_positive_of_rotated_em_lower {t δ e v : ℝ} {p : ℂ}
    (ht : |t| ≤ 12600) (hp : ‖p - criticalGammaPhase t‖ ≤ δ) (hδ : δ < 1)
    (he : |(eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63 * p).re - v| ≤ e)
    (hv : e + ‖p‖ / 1000000000000000000 < v) :
    0 < normalizedCriticalZeta t := by
  apply (rotated_critical_pos_iff hp hδ).mp
  have hr := (abs_le.mp (low_rotated_em_error ht p)).1
  have hc := (abs_le.mp he).1
  linarith

theorem low_negative_of_rotated_em_upper {t δ e v : ℝ} {p : ℂ}
    (ht : |t| ≤ 12600) (hp : ‖p - criticalGammaPhase t‖ ≤ δ) (hδ : δ < 1)
    (he : |(eulerMaclaurinApprox (criticalPoint t) (lowPrefix t) 63 * p).re - v| ≤ e)
    (hv : v < -(e + ‖p‖ / 1000000000000000000)) :
    normalizedCriticalZeta t < 0 := by
  apply (rotated_critical_neg_iff hp hδ).mp
  have hr := (abs_le.mp (low_rotated_em_error ht p)).2
  have hc := (abs_le.mp he).2
  linarith

def startupRotation (t : ℚ) : ℂ :=
  exp (((startupArgumentCenter t : ℝ) : ℂ) * I)

theorem startupRotation_error {t : ℚ} (htlo : 12570 ≤ t) (hthi : t ≤ 12580) :
    ‖startupRotation t - criticalGammaPhase (t : ℝ)‖ ≤ 1 / 10 := by
  rw [startupRotation, criticalGammaPhase_eq_exp_argument]
  have he := startupArgumentCenter_error htlo hthi
  rw [abs_sub_comm] at he
  exact (unitPhase_distance_le _ _).trans he

theorem norm_startupRotation (t : ℚ) : ‖startupRotation t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem startupRotation_pos_iff {t : ℚ} (htlo : 12570 ≤ t) (hthi : t ≤ 12580) :
    0 < (riemannZeta (criticalPoint (t : ℝ)) * startupRotation t).re ↔
      0 < normalizedCriticalZeta (t : ℝ) :=
  rotated_critical_pos_iff (startupRotation_error htlo hthi) (by norm_num)

theorem startupRotation_neg_iff {t : ℚ} (htlo : 12570 ≤ t) (hthi : t ≤ 12580) :
    (riemannZeta (criticalPoint (t : ℝ)) * startupRotation t).re < 0 ↔
      normalizedCriticalZeta (t : ℝ) < 0 :=
  rotated_critical_neg_iff (startupRotation_error htlo hthi) (by norm_num)

#print axioms rotated_critical_re
#print axioms rotated_critical_pos_iff
#print axioms low_positive_of_rotated_em_lower
#print axioms low_negative_of_rotated_em_upper
#print axioms startupRotation_pos_iff
#print axioms startupRotation_neg_iff

end LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate
