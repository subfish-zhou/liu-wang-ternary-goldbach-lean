import LiuWang.Proof.Campaign20260915.RosserCount.BacklundStripGamma

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_sinh_le_norm_sine (s : ℂ) :
    Real.sinh s.im ≤ ‖Complex.sin s‖ := by
  have h := norm_sub_norm_le (Complex.exp (-s * I)) (Complex.exp (s * I))
  simp only [Complex.norm_exp, mul_re, neg_re, neg_im, I_re, I_im, mul_zero,
    mul_one, zero_sub, neg_neg] at h
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, Real.sinh_eq]
  norm_num only [norm_ofNat]
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem backlund_sine_reference_le {s : ℂ} (ht : 0 < s.im) :
    ‖Complex.sin ((Real.pi : ℂ) * horizontalAt s.im 1 / 2)‖ ≤
      ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ * Real.exp (1 / s.im ^ 2) := by
  let y := Real.pi * s.im / 2
  have hy : s.im ≤ y := by dsimp [y]; nlinarith [Real.pi_gt_three]
  have hy0 : 0 < y := ht.trans_le hy
  have hs : s.im ≤ Real.sinh y := hy.trans (Real.self_le_sinh_iff.mpr hy0.le)
  have hs0 : 0 < Real.sinh y := ht.trans_le hs
  have ht2 : 0 < s.im ^ 2 := sq_pos_of_pos ht
  have hgap : Real.cosh y - Real.sinh y ≤ 1 / Real.sinh y := by
    rw [le_div_iff₀ hs0]
    nlinarith [Real.cosh_sq y, sq_nonneg (Real.cosh y - Real.sinh y)]
  have hi : 1 / Real.sinh y ≤ Real.sinh y / s.im ^ 2 := by
    rw [div_le_div_iff₀ hs0 ht2]
    nlinarith
  have he : Real.cosh y ≤ Real.sinh y * Real.exp (1 / s.im ^ 2) := by
    calc
      _ ≤ Real.sinh y + Real.sinh y / s.im ^ 2 := by linarith
      _ = Real.sinh y * (1 + 1 / s.im ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [add_comm] using Real.add_one_le_exp (1 / s.im ^ 2)) hs0.le
  have hn : Real.sinh y ≤ ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ := by
    simpa only [y, div_ofNat_im, mul_im, ofReal_re, ofReal_im, mul_zero, zero_mul, zero_add,
      add_zero] using backlund_sinh_le_norm_sine ((Real.pi : ℂ) * s / 2)
  have href : Complex.sin ((Real.pi : ℂ) * horizontalAt s.im 1 / 2) =
      (Real.cosh y : ℂ) := by
    have hr : ((Real.pi : ℂ) * horizontalAt s.im 1 / 2).re = Real.pi / 2 := by
      simp [horizontalAt]
    have hi' : ((Real.pi : ℂ) * horizontalAt s.im 1 / 2).im = y := by
      simp [horizontalAt, y]
    rw [Complex.sin_eq, hr, hi', ← ofReal_sin, ← ofReal_cos,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
    simp
  rw [href, norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos y)]
  exact he.trans (mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le)

#print axioms backlund_sinh_le_norm_sine
#print axioms backlund_sine_reference_le

end LiuWang.Proof.Campaign20260915.RosserCount
