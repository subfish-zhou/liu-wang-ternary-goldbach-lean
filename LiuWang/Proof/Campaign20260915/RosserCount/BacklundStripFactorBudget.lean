import LiuWang.Proof.Campaign20260915.RosserCount.BacklundStripSine

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

private theorem strip_gamma_pos {s : ℂ} (ht : 0 < s.im) : 0 < ‖Gamma (s / 2)‖ := by
  apply norm_pos_iff.mpr
  apply Gamma_ne_zero
  intro n he
  have h := congrArg Complex.im he
  simp only [div_ofNat_im, neg_im, natCast_im] at h
  linarith

private theorem strip_sine_pos {s : ℂ} (hs : 0 ≤ s.re) (hs' : s.re ≤ 1)
    (ht : 0 < s.im) : 0 < ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ :=
  norm_pos_iff.mpr (slitPlane_ne_zero (backlund_sine_mem_slitPlane hs hs' ht))

theorem backlundStripFactor_pos {s : ℂ} (hs : 0 ≤ s.re) (hs' : s.re ≤ 1)
    (ht : 0 < s.im) : 0 < ‖backlundStripFactor s‖ := by
  have hg := strip_gamma_pos ht
  have hn := strip_sine_pos hs hs' ht
  have h : 0 < ‖backlundStripFactor s‖ ^ 2 := by
    rw [backlundStripFactor_norm_sq]
    positivity
  nlinarith [norm_nonneg (backlundStripFactor s)]

theorem backlundStripFactor_log {s : ℂ} (hs : 0 ≤ s.re) (hs' : s.re ≤ 1)
    (ht : 0 < s.im) :
    2 * Real.log ‖backlundStripFactor s‖ =
      -s.re * Real.log Real.pi + 2 * Real.log ‖Gamma (s / 2)‖ +
        Real.log ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ := by
  have hg := strip_gamma_pos ht
  have hn := strip_sine_pos hs hs' ht
  have hp := Real.rpow_pos_of_pos Real.pi_pos (-s.re)
  have h := congrArg Real.log (backlundStripFactor_norm_sq s)
  rw [Real.log_mul (mul_ne_zero hp.ne' (pow_ne_zero 2 hg.ne')) hn.ne',
    Real.log_mul hp.ne' (pow_ne_zero 2 hg.ne'), Real.log_rpow Real.pi_pos] at h
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem backlundStripFactor_reciprocal_budget {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : 0 < s.im) :
    1 ≤ ‖backlundStripFactor s‖ *
      (s.im / (2 * Real.pi)) ^ ((1 - s.re) / 2) * Real.exp (3 / (2 * s.im ^ 2)) := by
  let v := horizontalAt s.im 1
  have hvre : v.re = 1 := by simp [v, horizontalAt]
  have hvim : v.im = s.im := by simp [v, horizontalAt]
  have hvt : 0 < v.im := by rwa [hvim]
  have hv0 : 0 ≤ v.re := by rw [hvre]; norm_num
  have hg := strip_gamma_pos ht
  have hgv := strip_gamma_pos hvt
  have hn := strip_sine_pos hs hs' ht
  have hnv := strip_sine_pos hv0 hvre.le hvt
  have hp : 0 < (s.im / 2) ^ ((1 - s.re) / 2) := by positivity
  have hq : 0 < s.im / (2 * Real.pi) := by positivity
  have hveq : v / 2 = horizontalAt (s.im / 2) (1 / 2) := by
    apply Complex.ext <;> simp [v, horizontalAt]
  have hgb := backlund_gamma_strip_reference hs hs' ht
  rw [← hveq] at hgb
  have hgl := Real.log_le_log hgv hgb
  rw [Real.log_mul (mul_ne_zero hg.ne' hp.ne') (Real.exp_pos _).ne',
    Real.log_mul hg.ne' hp.ne', Real.log_rpow (by positivity : 0 < s.im / 2),
    Real.log_exp] at hgl
  have hnb := backlund_sine_reference_le (s := s) ht
  change ‖Complex.sin ((Real.pi : ℂ) * v / 2)‖ ≤ _ at hnb
  have hnl := Real.log_le_log hnv hnb
  rw [Real.log_mul hn.ne' (Real.exp_pos _).ne', Real.log_exp] at hnl
  have hl := backlundStripFactor_log hs hs' ht
  have hlv := backlundStripFactor_log hv0 hvre.le hvt
  rw [backlundStripFactor_norm_one hvre hvt, Real.log_one, hvre] at hlv
  have hlog : Real.log (s.im / (2 * Real.pi)) =
      Real.log (s.im / 2) - Real.log Real.pi := by
    rw [show s.im / (2 * Real.pi) = (s.im / 2) / Real.pi by ring]
    exact Real.log_div (by positivity) Real.pi_ne_zero
  have hnonneg : 0 ≤ Real.log ‖backlundStripFactor s‖ +
      ((1 - s.re) / 2) * Real.log (s.im / (2 * Real.pi)) +
        3 / (2 * s.im ^ 2) := by
    rw [hlog]
    have he : 3 / (2 * s.im ^ 2) = 3 / 2 * (1 / s.im ^ 2) := by ring
    rw [he]
    nlinarith
  have he := Real.exp_le_exp.mpr hnonneg
  rw [Real.exp_zero, Real.exp_add, Real.exp_add,
    Real.exp_log (backlundStripFactor_pos hs hs' ht)] at he
  simpa only [Real.rpow_def_of_pos hq, mul_comm ((1 - s.re) / 2)] using he

theorem backlund_zeta_le_original_Phi_profile {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : 1 < s.im) :
    ‖riemannZeta s‖ ≤ ‖backlundStripPhi s‖ * ‖Complex.log (-s * I)‖ *
      (s.im / (2 * Real.pi)) ^ ((1 - s.re) / 2) * Real.exp (3 / (2 * s.im ^ 2)) := by
  have h := mul_le_mul_of_nonneg_right
    (backlundStripFactor_reciprocal_budget hs hs' (by linarith)) (norm_nonneg (riemannZeta s))
  have hn := norm_ne_zero_iff.mpr (backlund_log_base_ne_zero ht)
  have he : ‖backlundStripPhi s‖ * ‖Complex.log (-s * I)‖ =
      ‖backlundStripFactor s‖ * ‖riemannZeta s‖ := by
    rw [backlundStripPhi, norm_div, norm_mul, div_mul_cancel₀ _ hn]
  rw [he]
  simpa only [one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using h

#print axioms backlundStripFactor_pos
#print axioms backlundStripFactor_log
#print axioms backlundStripFactor_reciprocal_budget
#print axioms backlund_zeta_le_original_Phi_profile

end LiuWang.Proof.Campaign20260915.RosserCount
