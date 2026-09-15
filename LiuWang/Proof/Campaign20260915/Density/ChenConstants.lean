import LiuWang.Proof.Campaign20260915.Density.ChenInterpolation

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Density

theorem chen_exp_eight_thirds : Real.exp (8 / 3) ≤ 14.39192 := by
  have he1 : Real.exp 1 ≤ 2.718281829 :=
    Real.exp_one_lt_d9.le.trans (by norm_num)
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he1 8
  have he : Real.exp (8 / 3) ^ 3 = Real.exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have hn : (2.718281829 : ℝ) ^ 8 ≤ (14.39192 : ℝ) ^ 3 := by norm_num
  have h := hp.trans hn
  rw [← he] at h
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num)
    (by decide : (3 : ℕ) ≠ 0)).mp h

theorem chen_log_left_constant :
    Real.log 235.69 ≤ Real.log 42.6154 + (1 / 2) * Real.log 30.5879 := by
  have hs : (235.69 : ℝ) / 42.6154 ≤ Real.sqrt 30.5879 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hc : (235.69 : ℝ) ≤ 42.6154 * Real.sqrt 30.5879 := by
    simpa only [mul_comm] using (div_le_iff₀ (by norm_num : (0 : ℝ) < 42.6154)).mp hs
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 235.69) hc
  rw [Real.log_mul (by norm_num) (Real.sqrt_ne_zero'.mpr (by norm_num)),
    Real.log_sqrt (by norm_num)] at h
  linarith

theorem chen_log_right_constant :
    Real.log 90.5727 + 8 / 3 ≤ Real.log 42.6154 + Real.log 30.5879 := by
  have hc : (90.5727 : ℝ) * Real.exp (8 / 3) ≤ 42.6154 * 30.5879 := by
    exact (mul_le_mul_of_nonneg_left chen_exp_eight_thirds (by norm_num)).trans (by norm_num)
  have h := Real.log_le_log (show 0 < (90.5727 : ℝ) * Real.exp (8 / 3) by positivity) hc
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (by norm_num) (by norm_num)] at h
  exact h

theorem chen_shift_log_interpolation {a b L sigma : ℝ} (hL : 0 < L)
    (hs0 : 1 / 2 ≤ sigma) (hab : a - b ≤ 2 * L) :
    let theta := 3 * L * (2 * sigma - 1) / (3 * L + 4)
    (1 - theta) * a + theta * b ≤
      (2 - 2 * sigma) * a + (2 * sigma - 1) * b + (8 / 3) * (2 * sigma - 1) := by
  dsimp only
  let theta := 3 * L * (2 * sigma - 1) / (3 * L + 4)
  have ht0 : 0 ≤ 2 * sigma - 1 := by linarith
  have hden : 0 < 3 * L + 4 := by positivity
  have ht : theta ≤ 2 * sigma - 1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [ht0]
  have he : theta * (3 * L + 4) = 3 * L * (2 * sigma - 1) :=
    div_mul_cancel₀ _ hden.ne'
  have hgap : 2 * L * ((2 * sigma - 1) - theta) ≤ (8 / 3) * (2 * sigma - 1) := by
    nlinarith only [ht, he]
  have hm := mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr ht)
  change (1 - theta) * a + theta * b ≤ _
  nlinarith only [hm, hgap]

theorem chen_affine_endpoint_transport {a b K H delta sigma : ℝ}
    (hd : 0 ≤ delta) (hs0 : 1 / 2 ≤ sigma) (hs1 : sigma ≤ 1 + delta)
    (ha : a ≤ K + (1 / 2) * H) (hb : b ≤ K + (1 + delta) * H) :
    let theta := (sigma - 1 / 2) / (1 / 2 + delta)
    (1 - theta) * a + theta * b ≤ K + sigma * H := by
  let theta := (sigma - 1 / 2) / (1 / 2 + delta)
  have hden : 0 < 1 / 2 + delta := by linarith
  have ht0 : 0 ≤ theta := div_nonneg (by linarith) hden.le
  have ht1 : theta ≤ 1 := (div_le_one hden).mpr (by linarith)
  have he : theta * (1 / 2 + delta) = sigma - 1 / 2 := div_mul_cancel₀ _ hden.ne'
  change (1 - theta) * a + theta * b ≤ _
  calc
    _ ≤ (1 - theta) * (K + (1 / 2) * H) + theta * (K + (1 + delta) * H) :=
      add_le_add (mul_le_mul_of_nonneg_left ha (by linarith)) (mul_le_mul_of_nonneg_left hb ht0)
    _ = K + (1 / 2 + theta * (1 / 2 + delta)) * H := by ring
    _ = _ := by rw [he]; ring

#print axioms chen_log_left_constant
#print axioms chen_log_right_constant

end LiuWang.Proof.Campaign20260915.Density
