import LiuWang.Proof.Campaign20260915.RosserCount.BacklundUnitLine

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlundStripPhi_vertical_fifty {s : ℂ}
    (hs : s.re = 0 ∨ s.re = 1) (ht : 50 ≤ s.im) :
    ‖backlundStripPhi s‖ < 1 := by
  have ht0 : 0 < s.im := by linarith
  have hlog : Real.log s.im ≤ ‖Complex.log (-s * I)‖ := by
    have h := Real.log_le_log ht0 (im_le_norm s)
    have h' := re_le_norm (Complex.log (-s * I))
    rw [Complex.log_re, norm_mul, norm_neg, norm_I, mul_one] at h'
    exact h.trans h'
  have hlog0 : 0 < ‖Complex.log (-s * I)‖ :=
    (Real.log_pos (by linarith)).trans_le hlog
  rcases hs with hs | hs
  · let w : ℂ := 1 - conj s
    have hwr : w.re = 1 := by simp [w, hs]
    have hwi : w.im = s.im := by simp [w]
    have hwt : 0 < w.im := by rwa [hwi]
    have hz := backlund_zeta_unit_line hwr (by rw [hwi, abs_of_pos ht0]; exact ht)
    rw [hwi, abs_of_pos ht0] at hz
    have hf := backlundStripFactor_norm_one hwr hwt
    have hroot := backlund_sqrt_sine_transport ht0 hwi
    have hprod : ‖completedRiemannZeta s‖ *
        ‖Complex.sqrt (Complex.sin ((Real.pi : ℂ) * s / 2))‖ <
          (Real.log s.im - 1 / 10) * Real.exp (1 / s.im ^ 2) := by
      calc
        _ ≤ ‖completedRiemannZeta s‖ *
            (‖Complex.sqrt (Complex.sin ((Real.pi : ℂ) * w / 2))‖ *
              Real.exp (1 / s.im ^ 2)) :=
          mul_le_mul_of_nonneg_left hroot (norm_nonneg _)
        _ = ‖riemannZeta w‖ * Real.exp (1 / s.im ^ 2) := by
          rw [← backlund_completed_norm_reflect ht0.ne', ← mul_assoc,
            backlund_completed_sqrt_norm hwt.ne', hf, one_mul]
        _ < _ := mul_lt_mul_of_pos_right hz (Real.exp_pos _)
    have hx : 1 / s.im ^ 2 < (1 : ℝ) := by
      rw [div_lt_one (by positivity)]
      nlinarith
    have he := Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ 1 / s.im ^ 2) hx
    have he' : Real.exp (1 / s.im ^ 2) ≤ s.im ^ 2 / (s.im ^ 2 - 1) := by
      convert he using 1
      field_simp
    have hlt : (Real.log s.im - 1 / 10) * Real.exp (1 / s.im ^ 2) < Real.log s.im := by
      have hpos : 0 ≤ Real.log s.im - 1 / 10 := (norm_nonneg _).trans hz.le
      calc
        _ ≤ (Real.log s.im - 1 / 10) * (s.im ^ 2 / (s.im ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_left he' hpos
        _ < _ := by
          rw [← mul_div_assoc, div_lt_iff₀ (by nlinarith : 0 < s.im ^ 2 - 1)]
          have hl := Real.log_le_sub_one_of_pos ht0
          nlinarith
    rw [backlundStripPhi_completed (by linarith), norm_div, norm_mul]
    exact (div_lt_one hlog0).mpr ((hprod.trans hlt).trans_le hlog)
  · have hz := backlund_zeta_unit_line hs (by rw [abs_of_pos ht0]; exact ht)
    rw [abs_of_pos ht0] at hz
    rw [backlundStripPhi, norm_div, norm_mul, backlundStripFactor_norm_one hs ht0, one_mul]
    exact (div_lt_one hlog0).mpr (by linarith)

theorem exists_backlundStripPhi_fifty_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 50 ≤ s.im →
      ‖backlundStripPhi s‖ ≤ C * Real.exp (Real.pi * s.im / 2) := by
  obtain ⟨C, hC, hc⟩ := exists_completed_zeta_uniform_strip_bound
  refine ⟨C, hC, ?_⟩
  intro s hs hs' ht
  have ht0 : 0 < s.im := by linarith
  have hb := hc s hs hs' (by rw [abs_of_pos ht0]; linarith)
  let z := (Real.pi : ℂ) * s / 2
  have hz : z.im = Real.pi * s.im / 2 := by simp [z]
  have hz0 : 0 ≤ z.im := by rw [hz]; positivity
  have he : Real.cosh z.im ≤ Real.exp z.im := by
    rw [Real.cosh_eq]
    linarith [Real.exp_le_exp.mpr (show -z.im ≤ z.im by linarith)]
  have hn := (backlund_sine_norm_le_cosh z).trans he
  have hsq : ‖Complex.sqrt (Complex.sin z)‖ ^ 2 = ‖Complex.sin z‖ := by
    rw [Complex.sqrt, show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, Real.sq_sqrt (norm_nonneg _)]
  have hroot : ‖Complex.sqrt (Complex.sin z)‖ ≤ Real.exp z.im := by
    have h := Real.one_le_exp_iff.mpr hz0
    nlinarith [norm_nonneg (Complex.sqrt (Complex.sin z)), Real.exp_pos z.im]
  have hl : 1 ≤ ‖Complex.log (-s * I)‖ := by
    have h3 := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : 3 ≤ s.im)
    have hln := Real.log_le_log ht0 (im_le_norm s)
    have hr := re_le_norm (Complex.log (-s * I))
    rw [Complex.log_re, norm_mul, norm_neg, norm_I, mul_one] at hr
    linarith [Real.log_three_gt_d9]
  rw [backlundStripPhi_completed (by linarith), norm_div, norm_mul]
  calc
    _ ≤ ‖completedRiemannZeta s‖ * ‖Complex.sqrt (Complex.sin z)‖ :=
      div_le_self (by positivity) hl
    _ ≤ C * Real.exp z.im := mul_le_mul hb hroot (norm_nonneg _) hC.le
    _ = _ := by rw [hz]

#print axioms backlundStripPhi_vertical_fifty
#print axioms exists_backlundStripPhi_fifty_growth

end LiuWang.Proof.Campaign20260915.RosserCount
