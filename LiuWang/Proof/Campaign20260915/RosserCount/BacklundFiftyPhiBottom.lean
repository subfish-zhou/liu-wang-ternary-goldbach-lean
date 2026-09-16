import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFiftyPhiRight

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_completed_norm {s : ℂ} (ht : s.im ≠ 0) :
    ‖completedRiemannZeta s‖ =
      Real.pi ^ (-s.re / 2) * ‖Gamma (s / 2)‖ * ‖riemannZeta s‖ := by
  have hs : s ≠ 0 := by
    intro he
    exact ht (by rw [he, zero_im])
  have hg : Gamma (s / 2) ≠ 0 := by
    apply Gamma_ne_zero
    intro n he
    have hi := congrArg Complex.im he
    simp only [div_ofNat_im, neg_im, natCast_im, neg_zero] at hi
    exact ht (by linarith)
  have hp : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have he : completedRiemannZeta s =
      (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs, Gammaℝ_def]
    field_simp
  rw [he, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp only [div_ofNat_re, neg_re]

theorem backlund_completed_norm_reflect {s : ℂ} (ht : s.im ≠ 0) :
    ‖completedRiemannZeta (1 - conj s)‖ = ‖completedRiemannZeta s‖ := by
  rw [completedRiemannZeta_one_sub, backlund_completed_norm (by simpa using ht),
    backlund_completed_norm ht, conj_re, riemannZeta_conj, norm_conj]
  have he : conj s / 2 = conj (s / 2) := by
    apply Complex.ext
    · rw [conj_re]
      simp
    · rw [conj_im]
      simp [neg_div]
  rw [he, Gamma_conj, norm_conj]

theorem backlund_completed_sqrt_norm {s : ℂ} (ht : s.im ≠ 0) :
    ‖completedRiemannZeta s‖ * ‖Complex.sqrt (Complex.sin ((Real.pi : ℂ) * s / 2))‖ =
      ‖backlundStripFactor s‖ * ‖riemannZeta s‖ := by
  rw [backlund_completed_norm ht, backlundStripFactor, norm_mul, norm_mul,
    norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp only [div_ofNat_re, neg_re]
  ring

theorem backlund_sqrt_sine_transport {s w : ℂ}
    (ht : 0 < s.im) (hw : w.im = s.im) :
    ‖Complex.sqrt (Complex.sin ((Real.pi : ℂ) * s / 2))‖ ≤
      ‖Complex.sqrt (Complex.sin ((Real.pi : ℂ) * w / 2))‖ *
        Real.exp (1 / s.im ^ 2) := by
  have hu : ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ ≤
      ‖Complex.sin ((Real.pi : ℂ) *
        LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalAt w.im 1 / 2)‖ := by
    rw [backlund_sine_norm_reference, hw]
    simpa using backlund_sine_norm_le_cosh ((Real.pi : ℂ) * s / 2)
  have hl := hu.trans (backlund_sine_reference_le (by rwa [hw] : 0 < w.im))
  rw [hw] at hl
  have hsq (z : ℂ) : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by
    rw [Complex.sqrt, show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, Real.sq_sqrt (norm_nonneg _)]
  rw [← hsq (Complex.sin ((Real.pi : ℂ) * s / 2)),
    ← hsq (Complex.sin ((Real.pi : ℂ) * w / 2))] at hl
  have he : 1 ≤ Real.exp (1 / s.im ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have he2 : Real.exp (1 / s.im ^ 2) ≤ Real.exp (1 / s.im ^ 2) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left he2
    (sq_nonneg ‖Complex.sqrt (Complex.sin ((Real.pi : ℂ) * w / 2))‖)
  have hp := mul_nonneg (norm_nonneg (Complex.sqrt (Complex.sin ((Real.pi : ℂ) * w / 2))))
    (Real.exp_pos (1 / s.im ^ 2)).le
  nlinarith [norm_nonneg (Complex.sqrt (Complex.sin ((Real.pi : ℂ) * s / 2)))]

theorem backlundStripPhi_fifty_bottom {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : s.im = 50) :
    ‖backlundStripPhi s‖ < 1 := by
  by_cases hr : 1 / 2 ≤ s.re
  · exact backlundStripPhi_fifty_right hr hs' ht
  let w : ℂ := 1 - conj s
  have hwr : w.re = 1 - s.re := by simp [w]
  have hwi : w.im = s.im := by simp [w]
  have hwt : w.im = 50 := hwi.trans ht
  have hw : 1 / 2 ≤ w.re := by rw [hwr]; linarith
  have hw' : w.re ≤ 1 := by rw [hwr]; linarith
  have ht0 : 0 < s.im := by rw [ht]; norm_num
  have hz := backlund_fifty_zeta_bound hw hw' hwt
  have hf := backlundStripFactor_fifty_upper hw hw' hwt
  have hprod : ‖backlundStripFactor w‖ * ‖riemannZeta w‖ < (707 / 200 : ℝ) := by
    have h := (mul_le_mul_of_nonneg_right hf (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left hz (by norm_num : (0 : ℝ) < 101 / 100))
    norm_num at h ⊢
    exact h
  have hroot := backlund_sqrt_sine_transport ht0 hwi
  have he : Real.exp (1 / s.im ^ 2) ≤ (1001 / 1000 : ℝ) := by
    rw [ht]
    exact (Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 50 ^ 2) (by norm_num : (1 : ℝ) / 50 ^ 2 < 1)).trans
        (by norm_num)
  have hnum : ‖completedRiemannZeta s‖ *
      ‖Complex.sqrt (Complex.sin ((Real.pi : ℂ) * s / 2))‖ <
        (707 / 200 : ℝ) * (1001 / 1000) := by
    calc
      _ ≤ ‖completedRiemannZeta s‖ *
          (‖Complex.sqrt (Complex.sin ((Real.pi : ℂ) * w / 2))‖ * Real.exp (1 / s.im ^ 2)) :=
        mul_le_mul_of_nonneg_left hroot (norm_nonneg _)
      _ = (‖backlundStripFactor w‖ * ‖riemannZeta w‖) * Real.exp (1 / s.im ^ 2) := by
        rw [← backlund_completed_norm_reflect ht0.ne', ← mul_assoc,
          backlund_completed_sqrt_norm (by rw [hwt]; norm_num)]
      _ ≤ (‖backlundStripFactor w‖ * ‖riemannZeta w‖) * (1001 / 1000) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ < _ := mul_lt_mul_of_pos_right hprod (by norm_num)
  have hlog : (89 / 25 : ℝ) < ‖Complex.log (-s * I)‖ := by
    have hn : (50 : ℝ) ≤ ‖s‖ := by simpa [ht] using im_le_norm s
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 50) hn
    have h := re_le_norm (Complex.log (-s * I))
    rw [Complex.log_re, norm_mul, norm_neg, norm_I, mul_one] at h
    linarith [backlund_log_fifty_lower]
  rw [backlundStripPhi_completed (by rw [ht]; norm_num), norm_div, norm_mul]
  exact (div_lt_one (by linarith)).mpr (by linarith)

#print axioms backlund_completed_norm
#print axioms backlund_completed_norm_reflect
#print axioms backlund_completed_sqrt_norm
#print axioms backlund_sqrt_sine_transport
#print axioms backlundStripPhi_fifty_bottom

end LiuWang.Proof.Campaign20260915.RosserCount
