import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.BandDomain

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart

def densityKernel (H y : ℝ) : ℝ :=
  (254231 / y + 33643) * y ^ (6 : ℕ) * (H / (H - 4 * y)) *
    Real.exp (-y / 2 - 0.478 * H / y)

theorem shifted_height_bounds {t y k : ℝ} (ht : 1 ≤ t) (hy : 20 ≤ y)
    (hk : 0 ≤ k) (hk7 : k ≤ 7) :
    0 < y + k * Real.log t ∧ y ≤ y + k * Real.log t ∧
      y + k * Real.log t ≤ t * y := by
  have hl := Real.log_nonneg ht
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
  have hm := mul_le_mul hk7 hlog hl (by norm_num : (0 : ℝ) ≤ 7)
  have hp := mul_nonneg (by linarith : 0 ≤ t - 1) (by linarith : 0 ≤ y - 7)
  exact ⟨by positivity, le_add_of_nonneg_right (mul_nonneg hk hl), by nlinarith only [hm, hp]⟩

theorem shifted_phase_gain {H H₀ t y k : ℝ} (hH₀ : 3093 ≤ H₀)
    (ht : 1 ≤ t) (hH : H₀ * t ≤ H) (hy : 20 ≤ y) (hy60 : y ≤ 60)
    (hk : 0 ≤ k) (hk7 : k ≤ 7) :
    H₀ / y + 22 * Real.log t ≤ H / (y + k * Real.log t) := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := by linarith
  have hh := shifted_height_bounds ht hy hk hk7
  have hl := Real.log_nonneg ht
  have hcoef : 7 * H₀ + 22 * y ^ (2 : ℕ) ≤ H₀ * y := by
    have h1 := mul_nonneg (by linarith : 0 ≤ H₀) (by linarith : 0 ≤ y - 20)
    have h2 := mul_nonneg (by positivity : 0 ≤ y) (by linarith : 0 ≤ 60 - y)
    have h3 := mul_nonneg (by linarith : 0 ≤ 0.65 * H₀ - 1320) hy0.le
    nlinarith only [h1, h2, h3]
  have hquad : 154 * y ≤ H₀ * y / 2 := by
    have hh' := mul_nonneg (by linarith : 0 ≤ H₀ / 2 - 154) hy0.le
    nlinarith only [hh']
  have he := Real.quadratic_le_exp_of_nonneg hl
  rw [Real.exp_log ht0] at he
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ H₀ * y)
  have hlin := mul_le_mul_of_nonneg_right hcoef hl
  have hquadratic := mul_le_mul_of_nonneg_right hquad (sq_nonneg (Real.log t))
  have hbase : (H₀ / y + 22 * Real.log t) * (y + 7 * Real.log t) ≤ H₀ * t := by
    apply (mul_le_mul_iff_right₀ hy0).mp
    field_simp
    nlinarith only [hm, hlin, hquadratic]
  apply (le_div_iff₀ hh.1).mpr
  apply le_trans _ (hbase.trans hH)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  gcongr

theorem densityKernel_scaled {H H₀ t y k : ℝ} (hH₀ : 3093 ≤ H₀)
    (ht : 1 ≤ t) (hH : H₀ * t ≤ H) (hy : 20 ≤ y) (hy60 : y ≤ 60)
    (hk : 0 ≤ k) (hk7 : k ≤ 7) :
    densityKernel H (y + k * Real.log t) ≤
      t ^ (6 : ℕ) * Real.exp (-10.516 * Real.log t) * densityKernel H₀ y := by
  let z := y + k * Real.log t
  have hz := shifted_height_bounds ht hy hk hk7
  have hy0 : 0 < y := by linarith
  have ht0 : 0 < t := by linarith
  have hH0 : 0 < H₀ := by linarith
  have hHp : 0 < H := (mul_pos hH0 ht0).trans_le hH
  have hd0 : 0 < H₀ - 4 * y := by linarith
  have hd : 0 < H - 4 * z := by
    have hh := mul_pos hd0 ht0
    dsimp [z]
    nlinarith only [hh, hH, hz.2.2]
  have hr : H / (H - 4 * z) ≤ H₀ / (H₀ - 4 * y) := by
    apply (div_le_div_iff₀ hd hd0).mpr
    have hh1 := mul_le_mul_of_nonneg_left hz.2.2 hH0.le
    have hh2 := mul_le_mul_of_nonneg_right hH hy0.le
    dsimp [z]
    nlinarith only [hh1, hh2]
  have hc : 254231 / z + 33643 ≤ 254231 / y + 33643 := by
    gcongr
    exact hz.2.1
  have hp : z ^ (6 : ℕ) ≤ t ^ (6 : ℕ) * y ^ (6 : ℕ) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hz.1.le hz.2.2 _
  have he : Real.exp (-z / 2 - 0.478 * H / z) ≤
      Real.exp (-10.516 * Real.log t) * Real.exp (-y / 2 - 0.478 * H₀ / y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := shifted_phase_gain hH₀ ht hH hy hy60 hk hk7
    dsimp [z]
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith only [hh, hz.2.1]
  unfold densityKernel
  change (254231 / z + 33643) * z ^ (6 : ℕ) * (H / (H - 4 * z)) *
    Real.exp (-z / 2 - 0.478 * H / z) ≤ _
  calc
    _ ≤ (254231 / y + 33643) * (t ^ (6 : ℕ) * y ^ (6 : ℕ)) *
        (H₀ / (H₀ - 4 * y)) *
        (Real.exp (-10.516 * Real.log t) * Real.exp (-y / 2 - 0.478 * H₀ / y)) := by
      apply mul_le_mul _ he (Real.exp_pos _).le (by positivity)
      apply mul_le_mul _ hr (by positivity) (by positivity)
      exact mul_le_mul hc hp (by positivity) (by positivity)
    _ = _ := by ring

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
