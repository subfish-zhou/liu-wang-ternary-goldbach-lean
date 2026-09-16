import LiuWang.Proof.Campaign20260915.RosserCount.BacklundStripPhi
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundOuterReduction

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlundStripFactor_norm_zero {s : ℂ} (hs : s.re = 0) (ht : 0 < s.im) :
    ‖backlundStripFactor s‖ ^ 2 * s.im = 2 * Real.pi := by
  have hn : Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0 :=
    slitPlane_ne_zero (backlund_sine_mem_slitPlane hs.ge (by rw [hs]; norm_num) ht)
  have hconj : 1 - s / 2 = conj (s / 2) + 1 := by
    apply Complex.ext
    · rw [add_re, conj_re, sub_re, one_re, div_ofNat_re, hs]
      norm_num
    · rw [add_im, conj_im, sub_im, one_im, div_ofNat_im]
      ring
  have hz : conj (s / 2) ≠ 0 := by
    intro he
    have h := congrArg Complex.im he
    simp only [conj_im, div_ofNat_im, zero_im] at h
    linarith
  have hnorm : ‖s‖ = s.im := by
    have h := Complex.sq_norm s
    rw [normSq_apply, hs] at h
    nlinarith [norm_nonneg s]
  have h := congrArg norm (Gamma_mul_Gamma_one_sub (s / 2))
  rw [hconj, Gamma_add_one _ hz, Gamma_conj] at h
  simp only [norm_mul, norm_conj, norm_div, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at h
  rw [show (Real.pi : ℂ) * (s / 2) = (Real.pi : ℂ) * s / 2 by ring] at h
  have hh : ‖Gamma (s / 2)‖ * (s.im / 2 * ‖Gamma (s / 2)‖) *
      ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ = Real.pi := by
    have h' := (eq_div_iff (norm_ne_zero_iff.mpr hn)).mp h
    simpa only [norm_div, norm_ofNat, hnorm] using h'
  have hf := backlundStripFactor_norm_sq s
  rw [hs, neg_zero, Real.rpow_zero, one_mul] at hf
  linear_combination (congrArg (fun x : ℝ => x * s.im) hf) + 2 * hh

theorem backlundStripPhi_left_lt_one {s : ℂ} (hs : s.re = 0)
    (ht : 1000 ≤ s.im) :
    ‖backlundStripPhi s‖ < 1 := by
  have ht0 : 0 < s.im := by linarith
  have hfactor := backlundStripFactor_norm_zero hs ht0
  have hf : 0 < ‖backlundStripFactor s‖ := by
    have h := norm_nonneg (backlundStripFactor s)
    by_contra hbad
    have hz : ‖backlundStripFactor s‖ = 0 := le_antisymm (le_of_not_gt hbad) h
    rw [hz] at hfactor
    nlinarith [Real.pi_pos]
  have hq : 0 ≤ (s.im / (2 * Real.pi)) ^ (1 / 2 : ℝ) := by positivity
  have hq2 : ((s.im / (2 * Real.pi)) ^ (1 / 2 : ℝ)) ^ 2 =
      s.im / (2 * Real.pi) := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  have hp : ‖backlundStripFactor s‖ *
      (s.im / (2 * Real.pi)) ^ (1 / 2 : ℝ) = 1 := by
    have hsq : (‖backlundStripFactor s‖ *
        (s.im / (2 * Real.pi)) ^ (1 / 2 : ℝ)) ^ 2 = 1 := by
      rw [mul_pow, hq2]
      calc
        _ = (‖backlundStripFactor s‖ ^ 2 * s.im) / (2 * Real.pi) := by ring
        _ = 1 := by rw [hfactor, div_self (by positivity)]
    nlinarith [mul_nonneg (norm_nonneg (backlundStripFactor s)) hq]
  have hz := backlund_zeta_left_growth (s := s) (by rw [hs]; norm_num) hs.le
    (by rwa [abs_of_pos ht0])
  rw [hs, sub_zero, abs_of_pos ht0] at hz
  have hb := mul_lt_mul_of_pos_left hz hf
  rw [← mul_assoc, hp, one_mul] at hb
  have hl : Real.log s.im ≤ ‖Complex.log (-s * I)‖ := by
    calc
      _ ≤ Real.log ‖s‖ := Real.log_le_log ht0 (im_le_norm s)
      _ = (Complex.log (-s * I)).re := by
        rw [Complex.log_re, norm_mul, norm_neg, norm_I, mul_one]
      _ ≤ _ := re_le_norm _
  rw [backlundStripPhi, norm_div, norm_mul]
  exact (div_lt_one (norm_pos_iff.mpr (backlund_log_base_ne_zero (by linarith)))).mpr
    (hb.trans_le hl)

theorem backlundStripPhi_vertical_lt_one {s : ℂ}
    (hs : s.re = 0 ∨ s.re = 1) (ht : 1000 ≤ s.im) :
    ‖backlundStripPhi s‖ < 1 := by
  rcases hs with hs | hs
  · exact backlundStripPhi_left_lt_one hs ht
  · exact backlundStripPhi_right_lt_one hs ht

#print axioms backlundStripFactor_norm_zero
#print axioms backlundStripPhi_left_lt_one
#print axioms backlundStripPhi_vertical_lt_one

end LiuWang.Proof.Campaign20260915.RosserCount
