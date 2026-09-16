import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFiftyOriginal
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundStripGrowth

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_sine_norm_le_cosh (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.cosh z.im := by
  have h := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  simp only [Complex.norm_exp, mul_re, neg_re, neg_im, I_re, I_im, mul_zero,
    mul_one, zero_sub, neg_neg] at h
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, Real.cosh_eq]
  norm_num only [norm_ofNat]
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem backlund_sine_norm_reference (t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * horizontalAt t 1 / 2)‖ = Real.cosh (Real.pi * t / 2) := by
  have hr : ((Real.pi : ℂ) * horizontalAt t 1 / 2).re = Real.pi / 2 := by
    simp [horizontalAt]
  have hi : ((Real.pi : ℂ) * horizontalAt t 1 / 2).im = Real.pi * t / 2 := by
    simp [horizontalAt]
  rw [Complex.sin_eq, hr, hi, ← ofReal_sin, ← ofReal_cos,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [← ofReal_cosh]
  norm_num only [ofReal_one, ofReal_zero, one_mul, zero_mul, add_zero, norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]

theorem backlundStripFactor_right_upper {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 1) (ht : 50 ≤ s.im) :
    ‖backlundStripFactor s‖ ≤ Real.exp (129 / (32 * s.im ^ 2)) := by
  have hs0 : 0 ≤ s.re := by linarith
  have ht0 : 0 < s.im := by linarith
  let v := horizontalAt s.im 1
  have hvre : v.re = 1 := by simp [v, horizontalAt]
  have hvim : v.im = s.im := by simp [v, horizontalAt]
  have hvt : 0 < v.im := by rwa [hvim]
  have hv0 : 0 ≤ v.re := by rw [hvre]; norm_num
  have hveq : v / 2 = horizontalAt (s.im / 2) (1 / 2) := by
    apply Complex.ext <;> simp [v, horizontalAt]
  have hseq : s / 2 = horizontalAt (s.im / 2) (s.re / 2) := by
    apply Complex.ext <;> simp [horizontalAt]
  have hg := (abs_le.mp (backlund_log_gamma_ratio_error
    (a := s.re / 2) (b := 1 / 2) (y := s.im / 2)
    (by linarith) (by linarith) (by norm_num) (by positivity))).1
  rw [← hveq, ← hseq] at hg
  have herror : 129 / (32 * (s.im / 2) ^ 2) * (1 / 2 - s.re / 2) ≤
      129 / (32 * s.im ^ 2) := by
    have hsmall : 1 / 2 - s.re / 2 ≤ 1 / 4 := by linarith
    calc
      _ ≤ 129 / (32 * (s.im / 2) ^ 2) * (1 / 4) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by ring
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ ≤
      ‖Complex.sin ((Real.pi : ℂ) * v / 2)‖ := by
    rw [show v = horizontalAt s.im 1 by rfl, backlund_sine_norm_reference]
    simpa using backlund_sine_norm_le_cosh ((Real.pi : ℂ) * s / 2)
  have hn : 0 < ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ :=
    norm_pos_iff.mpr (slitPlane_ne_zero (backlund_sine_mem_slitPlane hs0 hs' ht0))
  have hl := Real.log_le_log hn hsin
  have hfactor := backlundStripFactor_log hs0 hs' ht0
  have href := backlundStripFactor_log hv0 hvre.le hvt
  rw [backlundStripFactor_norm_one hvre hvt, Real.log_one, hvre] at href
  have hylog : Real.log Real.pi ≤ Real.log (s.im / 2) :=
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
  have hlog : Real.log ‖backlundStripFactor s‖ ≤ 129 / (32 * s.im ^ 2) := by
    have hnonpos : (1 - s.re) * (Real.log Real.pi - Real.log (s.im / 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith
  exact (Real.log_le_iff_le_exp (backlundStripFactor_pos hs0 hs' ht0)).mp hlog

theorem backlundStripFactor_fifty_upper {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 1) (ht : s.im = 50) :
    ‖backlundStripFactor s‖ ≤ 101 / 100 := by
  have h := backlundStripFactor_right_upper hs hs' (by rw [ht])
  rw [ht] at h
  have he := Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0 : ℝ) ≤ 129 / (32 * 50 ^ 2))
    (by norm_num : (129 : ℝ) / (32 * 50 ^ 2) < 1)
  exact h.trans (he.trans (by norm_num))

theorem backlundStripPhi_fifty_right {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 1) (ht : s.im = 50) :
    ‖backlundStripPhi s‖ < 1 := by
  have hf := backlundStripFactor_fifty_upper hs hs' ht
  have hz := backlund_fifty_zeta_bound hs hs' ht
  have hprod : ‖backlundStripFactor s‖ * ‖riemannZeta s‖ < (101 / 100 : ℝ) * (7 / 2) :=
    (mul_le_mul_of_nonneg_right hf (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left hz (by norm_num))
  have hlog : (89 / 25 : ℝ) < ‖Complex.log (-s * I)‖ := by
    have hnorm : (50 : ℝ) ≤ ‖s‖ := by simpa [ht] using im_le_norm s
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 50) hnorm
    have hr := re_le_norm (Complex.log (-s * I))
    rw [Complex.log_re, norm_mul, norm_neg, norm_I, mul_one] at hr
    linarith [backlund_log_fifty_lower]
  rw [backlundStripPhi, norm_div, norm_mul]
  exact (div_lt_one (by linarith)).mpr (by linarith)

#print axioms backlund_sine_norm_le_cosh
#print axioms backlund_sine_norm_reference
#print axioms backlundStripFactor_right_upper
#print axioms backlundStripFactor_fifty_upper
#print axioms backlundStripPhi_fifty_right

end LiuWang.Proof.Campaign20260915.RosserCount
