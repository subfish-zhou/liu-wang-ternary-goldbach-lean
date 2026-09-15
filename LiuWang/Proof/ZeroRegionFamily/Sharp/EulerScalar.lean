import LiuWang.Proof.ZeroRegionFamily.Sharp.Gamma

/-! # 同权重Euler因子差：先抵消，再一次支付正权费用 -/

set_option autoImplicit false
noncomputable section

open Complex

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

theorem norm_geometric_difference_le {a b k : ℝ} (ha : 0 ≤ a) (hba : b ≤ a)
    (hb : 0 ≤ b) (ha1 : a < 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(a : ℂ)*z/(1-(a : ℂ)*z)-
      (k : ℂ)*((b : ℂ)*z/(1-(b : ℂ)*z))‖ ≤ a/(1-a)-k*b/(1-b) := by
  have hb1 : b < 1 := hba.trans_lt ha1
  have hna : ‖(a : ℂ)*z‖ ≤ a := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
    simpa using mul_le_mul_of_nonneg_left hz ha
  have hnb : ‖(b : ℂ)*z‖ ≤ b := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb]
    simpa using mul_le_mul_of_nonneg_left hz hb
  have hda : 1-a ≤ ‖1-(a : ℂ)*z‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) ((a : ℂ)*z)
    rw [norm_one] at hh
    linarith
  have hdb : 1-b ≤ ‖1-(b : ℂ)*z‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) ((b : ℂ)*z)
    rw [norm_one] at hh
    linarith
  have hane : 1-(a : ℂ)*z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hda)
  have hbne : 1-(b : ℂ)*z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hdb)
  have hc : 0 ≤ a-k*b := by nlinarith [hk.2]
  have hd : 0 ≤ k*b*(a-b) := mul_nonneg (mul_nonneg hk.1 hb) (sub_nonneg.mpr hba)
  have hid : (a : ℂ)*z/(1-(a : ℂ)*z)-
      (k : ℂ)*((b : ℂ)*z/(1-(b : ℂ)*z)) =
      ((a-k*b : ℝ) : ℂ)*z/(1-(a : ℂ)*z)+
      ((k*b*(a-b) : ℝ) : ℂ)*z^2/((1-(a : ℂ)*z)*(1-(b : ℂ)*z)) := by
    push_cast
    simp only [← mul_div_assoc]
    field_simp [hane, hbne]
    ring_nf
    field_simp [show 1-z*(b : ℂ) ≠ 0 by simpa [mul_comm] using hbne]
    ring
  rw [hid]
  apply (norm_add_le _ _).trans
  have hfirst :
      ‖((a-k*b : ℝ) : ℂ)*z/(1-(a : ℂ)*z)‖ ≤ (a-k*b)/(1-a) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    apply div_le_div₀ hc
      (by simpa using mul_le_mul_of_nonneg_left hz hc) (by linarith) hda
  have hsecond :
      ‖((k*b*(a-b) : ℝ) : ℂ)*z^2/((1-(a : ℂ)*z)*(1-(b : ℂ)*z))‖ ≤
        k*b*(a-b)/((1-a)*(1-b)) := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hd]
    have hzz : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
    apply div_le_div₀ hd
      (by simpa using mul_le_mul_of_nonneg_left hzz hd) (by positivity)
      (mul_le_mul hda hdb (by linarith) (norm_nonneg _))
  have heq : (a-k*b)/(1-a)+k*b*(a-b)/((1-a)*(1-b)) = a/(1-a)-k*b/(1-b) := by
    field_simp [ne_of_gt (sub_pos.mpr ha1), ne_of_gt (sub_pos.mpr hb1)]
    ring
  linarith

theorem geometric_cost_nonneg {a b k : ℝ} (ha : 0 ≤ a) (hba : b ≤ a)
    (hb : 0 ≤ b) (ha1 : a < 1) (hk : k ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ a/(1-a)-k*b/(1-b) := by
  have hh := norm_geometric_difference_le ha hba hb ha1 hk (z := 0) (by simp)
  simpa using hh

end LiuWang.Proof.ZeroRegionFamily.Sharp
