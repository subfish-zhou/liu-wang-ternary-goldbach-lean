import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Scale

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

theorem small_power_scaling {s s₀ r : ℝ} (hs₀ : 24 ≤ s₀) (hr : 1 ≤ r)
    (hlo : s₀ ≤ s) (hhi : s ≤ s₀ * r) :
    s ^ (1 / 15 : ℝ) ≤ s₀ ^ (1 / 15 : ℝ) * r := by
  have hp := Real.rpow_le_rpow (by linarith : 0 ≤ s) hhi (by norm_num : (0 : ℝ) ≤ 1 / 15)
  rw [Real.mul_rpow (by linarith : 0 ≤ s₀) (by linarith : 0 ≤ r)] at hp
  have he := Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1 / 15 : ℝ) ≤ 1)
  rw [Real.rpow_one] at he
  exact hp.trans (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (by linarith) _))

theorem density_coefficient_scaling {s s₀ r : ℝ} (hs₀ : 24 ≤ s₀) (hr : 1 ≤ r)
    (hlo : s₀ ≤ s) (hhi : s ≤ s₀ * r) :
    (254231 / densityLog s + 17102) * densityLog s ^ 6 ≤
      ((254231 / densityLog s₀ + 17102) * densityLog s₀ ^ 6) * r ^ 6 := by
  have hs := heightLog_scaling hs₀ hr hlo hhi
  have hz₀ := (heightLog_bounds hs₀).2
  have hz := (heightLog_bounds (hs₀.trans hlo)).2
  have hc := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 254231)
    (by linarith : 0 < densityLog s₀) hs.2.2.1
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ densityLog s) hs.2.2.2 6
  have h := mul_le_mul (add_le_add_right hc 17102) hp
    (pow_nonneg (by linarith : 0 ≤ densityLog s) 6) (by positivity)
  rw [mul_pow] at h
  nlinarith only [h]

theorem first_amplitude_scaling {s s₀ r : ℝ} (hs₀ : 24 ≤ s₀) (hr : 1 ≤ r)
    (hlo : s₀ ≤ s) (hhi : s ≤ s₀ * r) :
    1.8771 * Real.exp (-(9 / 20 : ℝ) * s) * logNu s * s ^ (1 / 15 : ℝ) *
        (254231 / densityLog s + 17102) * densityLog s ^ 6 ≤
      (1.8771 * Real.exp (-(9 / 20 : ℝ) * s₀) * logNu s₀ * s₀ ^ (1 / 15 : ℝ) *
        (254231 / densityLog s₀ + 17102) * densityLog s₀ ^ 6) * r ^ 8 := by
  have hnu := (logNu_bounds (hs₀.trans hlo)).2
  have hnu₀ := (logNu_bounds hs₀).2
  have hz₀ := (heightLog_bounds hs₀).2
  have hz := (heightLog_bounds (hs₀.trans hlo)).2
  have hspos : 0 ≤ s := by linarith
  have hs₀pos : 0 ≤ s₀ := by linarith
  have hrpos : 0 ≤ r := by linarith
  have hE := Real.exp_le_exp.mpr (show -(9 / 20 : ℝ) * s ≤ -(9 / 20 : ℝ) * s₀ by linarith)
  have hN := logNu_scaling hs₀ hr hlo hhi
  have hP := small_power_scaling hs₀ hr hlo hhi
  have hD := density_coefficient_scaling hs₀ hr hlo hhi
  have h := mul_le_mul
    (mul_le_mul hE (mul_le_mul hN hP (Real.rpow_nonneg (by linarith) _) (by positivity))
      (by positivity) (Real.exp_pos _).le)
    hD (by positivity) (by positivity)
  have h := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1.8771)
  nlinarith only [h]

theorem second_amplitude_scaling {s s₀ r : ℝ} (hs₀ : 24 ≤ s₀) (hr : 1 ≤ r)
    (hlo : s₀ ≤ s) (hhi : s ≤ s₀ * r) :
    1.0159 * 16541 * Real.exp (-(1 / 2 : ℝ) * s) * logNu s * heightLog s ^ 6 ≤
      (1.0159 * 16541 * Real.exp (-(1 / 2 : ℝ) * s₀) * logNu s₀ * heightLog s₀ ^ 6) *
        r ^ 8 := by
  have hnu := (logNu_bounds (hs₀.trans hlo)).2
  have hnu₀ := (logNu_bounds hs₀).2
  have hs := heightLog_scaling hs₀ hr hlo hhi
  have hh := (heightLog_bounds (hs₀.trans hlo)).1
  have hE := Real.exp_le_exp.mpr (show -(1 / 2 : ℝ) * s ≤ -(1 / 2 : ℝ) * s₀ by linarith)
  have hP := pow_le_pow_left₀ (by linarith : 0 ≤ heightLog s) hs.2.1 6
  have hN := logNu_scaling hs₀ hr hlo hhi
  have h := mul_le_mul (mul_le_mul hE hN hnu (Real.exp_pos _).le) hP
    (pow_nonneg (by linarith) 6) (by positivity)
  have h := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1.0159 * 16541)
  have hp := pow_le_pow_right₀ hr (by norm_num : (7 : ℕ) ≤ 8)
  have hp := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 1.0159 * 16541 * Real.exp (-(1 / 2 : ℝ) * s₀) * logNu s₀ * heightLog s₀ ^ 6 by positivity)
  rw [mul_pow] at h
  nlinarith only [h, hp]

theorem originalBracket_reduce_L {L x : ℝ} (hL : 3100 ≤ L)
    (hx : 3 ≤ x) (hx1 : x ≤ 6) :
    originalBracket L x ≤ originalBracket 3100 x := by
  let s := x * Real.log L
  let s₀ := x * Real.log 3100
  let r := L / 3100
  let A (v : ℝ) := 1.8771 * Real.exp (-(9 / 20 : ℝ) * v) * logNu v * v ^ (1 / 15 : ℝ) *
    (254231 / densityLog v + 17102) * densityLog v ^ 6 +
      1.0159 * 16541 * Real.exp (-(1 / 2 : ℝ) * v) * logNu v * heightLog v ^ 6
  have hr : 1 ≤ r := by dsimp only [r]; linarith
  have hs := real_parameter_scaling hL hx hx1
  have hA : A s ≤ A s₀ * r ^ 8 := by
    have h1 := first_amplitude_scaling hs.1 hr hs.2.2.1 hs.2.2.2
    have h2 := second_amplitude_scaling hs.1 hr hs.2.2.1 hs.2.2.2
    dsimp only [A]
    linarith
  have hnu₀ := (logNu_bounds hs.1).2
  have hz₀ := (heightLog_bounds hs.1).2
  have hA₀ : 0 ≤ A s₀ := by dsimp only [A, s₀]; positivity
  have hE := common_exponential_scaling hL hx hx1
  have hL0 : 0 < L := by linarith
  rw [originalBracket_eq_logBracket hL0 (by linarith) (Real.log_pos (by linarith)),
    originalBracket_eq_logBracket (by norm_num : (0 : ℝ) < 3100) (by linarith)
      (Real.log_pos (by norm_num))]
  change L * A s * Real.exp (-0.478 * L / (s + Real.log lowHeight)) ≤
    3100 * A s₀ * Real.exp (-0.478 * 3100 / (s₀ + Real.log lowHeight))
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hA hL0.le) hE
    (Real.exp_pos _).le (by positivity)
  apply hprod.trans
  have hp : r ^ 9 ≤ r ^ 10 := pow_le_pow_right₀ hr (by norm_num)
  have heq : L * (A s₀ * r ^ 8) *
      (Real.exp (-0.478 * 3100 / (s₀ + Real.log lowHeight)) / r ^ 10) =
      (3100 * A s₀ * Real.exp (-0.478 * 3100 / (s₀ + Real.log lowHeight))) *
        (r ^ 9 / r ^ 10) := by
    have hLr : L = 3100 * r := by dsimp only [r]; ring
    rw [hLr]
    ring
  rw [heq]
  have hfrac : r ^ 9 / r ^ 10 ≤ 1 :=
    (div_le_one (pow_pos (by linarith : 0 < r) 10)).mpr hp
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac (by positivity :
    0 ≤ 3100 * A s₀ * Real.exp (-0.478 * 3100 / (s₀ + Real.log lowHeight)))

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
