import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.HalfStripMaximum

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation

def sourceStripNormEnvelope (s : ℂ) : ℝ :=
  ‖sourceStripNormalizer s‖ * Real.exp (sourceStripBoundaryExponent s).re *
    ‖sourceBottomBarrier s‖ / ‖s - 1‖

theorem sourceHalfStripQuotient_norm_identity (s : ℂ) :
    ‖sourceHalfStripQuotient s‖ *
        (‖sourceStripNormalizer s‖ * Real.exp (sourceStripBoundaryExponent s).re *
          ‖sourceBottomBarrier s‖) =
      ‖s - 1‖ * ‖riemannZeta s‖ := by
  have hD := norm_ne_zero_iff.mpr (sourceStripNormalizer_ne_zero s)
  have hE := norm_ne_zero_iff.mpr (sourceBottomBarrier_ne_zero s)
  rw [sourceHalfStripQuotient, sourceStripQuotient, norm_div, norm_div,
    norm_mul, norm_mul, Complex.norm_exp]
  field_simp

theorem sourceCriticalQuotient_scale_le {t : ℝ} (ht : 0 < t) :
    (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) *
      ‖sourceHalfStripQuotient (criticalPoint t)‖ ≤ ‖riemannZeta (criticalPoint t)‖ := by
  have hs : (criticalPoint t).re = 1 / 2 := by simp [criticalPoint]
  have hi : (criticalPoint t).im = t := by simp [criticalPoint]
  have hn : 0 < ‖criticalPoint t‖ := norm_pos_iff.mpr (criticalPoint_ne_zero t)
  have hD := sourceStripNormalizer_norm_lower (s := criticalPoint t)
    (by rw [hs]; norm_num) (by rwa [hi])
  norm_num [hs] at hD
  have hpow : ‖criticalPoint t‖ ^ (5 / 4 : ℝ) =
      ‖criticalPoint t‖ * ‖criticalPoint t‖ ^ (1 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hn, Real.rpow_one]
  rw [hpow] at hD
  have hB : Real.exp (sourceStripBoundaryExponent (criticalPoint t)).re = 253 / 100 := by
    rw [sourceStripBoundaryExponent_re, hs]
    norm_num
    exact Real.exp_log (by norm_num)
  have hE := sourceBottomBarrier_norm_ge_one (s := criticalPoint t)
    (by rw [hs]; constructor <;> norm_num)
  have hroot : t ^ (1 / 4 : ℝ) ≤ ‖criticalPoint t‖ ^ (1 / 4 : ℝ) := by
    apply Real.rpow_le_rpow ht.le _ (by norm_num)
    simpa [hi, abs_of_pos ht] using Complex.abs_im_le_norm (criticalPoint t)
  have hden :
      ‖criticalPoint t‖ * ((253 / 100 : ℝ) * t ^ (1 / 4 : ℝ)) ≤
        ‖sourceStripNormalizer (criticalPoint t)‖ *
          Real.exp (sourceStripBoundaryExponent (criticalPoint t)).re *
            ‖sourceBottomBarrier (criticalPoint t)‖ := by
    rw [hB]
    calc
      _ = (‖criticalPoint t‖ * t ^ (1 / 4 : ℝ)) * (253 / 100) := by ring
      _ ≤ ‖sourceStripNormalizer (criticalPoint t)‖ * (253 / 100) := by
        exact mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left hroot hn.le).trans hD) (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hE
  have he := sourceHalfStripQuotient_norm_identity (criticalPoint t)
  have heq : ‖criticalPoint t - 1‖ = ‖criticalPoint t‖ := by
    have hc : criticalPoint t - 1 = -star (criticalPoint t) := by
      apply Complex.ext <;> simp [criticalPoint]
      ring
    rw [hc, norm_neg, norm_star]
  rw [heq] at he
  have hm := mul_le_mul_of_nonneg_right hden (norm_nonneg (sourceHalfStripQuotient (criticalPoint t)))
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith

theorem sourceHalfStrip_violation_critical_witness {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 128 * Real.pi ≤ s.im)
    (hbad : 1 < ‖sourceHalfStripQuotient s‖) :
    ∃ t : ℝ, 128 * Real.pi ≤ t ∧
      (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖ := by
  obtain ⟨t, ht, hq⟩ := sourceHalfStrip_left_violation hs ht hbad
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have h := mul_lt_mul_of_pos_left hq
    (show 0 < (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) by positivity)
  rw [mul_one] at h
  exact ⟨t, ht, h.trans_le (sourceCriticalQuotient_scale_le ht0)⟩

theorem sourceStrip_norm_violation_critical_witness {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 128 * Real.pi ≤ s.im)
    (hbad : sourceStripNormEnvelope s < ‖riemannZeta s‖) :
    ∃ t : ℝ, 128 * Real.pi ≤ t ∧
      (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖ := by
  have hi : 0 < s.im := lt_of_lt_of_le (by positivity) ht
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hD := norm_pos_iff.mpr (sourceStripNormalizer_ne_zero s)
  have hE := norm_pos_iff.mpr (sourceBottomBarrier_ne_zero s)
  have hd : 0 < ‖sourceStripNormalizer s‖ *
      Real.exp (sourceStripBoundaryExponent s).re * ‖sourceBottomBarrier s‖ := by positivity
  have h := (div_lt_iff₀ (norm_pos_iff.mpr hs1)).mp hbad
  have he := sourceHalfStripQuotient_norm_identity s
  have hq : 1 < ‖sourceHalfStripQuotient s‖ := by nlinarith
  exact sourceHalfStrip_violation_critical_witness hs ht hq

#print axioms sourceCriticalQuotient_scale_le
#print axioms sourceHalfStrip_violation_critical_witness
#print axioms sourceStrip_norm_violation_critical_witness

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
