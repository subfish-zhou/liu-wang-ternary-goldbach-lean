import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityBeta
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityLogs

/-! Integration on the original high-beta interval, before any count assumption. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

theorem exp_density_shift_le : Real.exp (2.104 : ℝ) ≤ 9 := by
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le
    (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 2
  rw [← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat, mul_one] at h
  have he := Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0 : ℝ) ≤ 0.104) (by norm_num : (0.104 : ℝ) < 1)
  have hp := mul_le_mul h he (Real.exp_pos _).le (by norm_num)
  rw [← Real.exp_add] at hp
  norm_num at hp ⊢
  linarith

theorem integrated_density_envelope {L s z a : ℝ}
    (hL : 0 < L) (hs : 0 < s) (_hz : 0 ≤ z)
    (hzs : z ≤ (11 / 10) * s) (hgap : 4 * z ≤ L / 10) :
    (∫ alpha in a..(1 - 0.478 / s),
      L * Real.exp (L * (alpha - 1)) *
        (16541 * z ^ 6 + 24200 * z ^ 6 * Real.exp (4 * z * (1 - alpha)))) ≤
      (10 / 9) * (16541 + 9 * 24200) * z ^ 6 * Real.exp (-0.478 * L / s) := by
  have hk : 0 < L - 4 * z := by linarith
  have hfrac : L / (L - 4 * z) ≤ 10 / 9 := by
    apply (div_le_iff₀ hk).mpr
    linarith
  have h0 := integral_density_exponential (L := L) (D := 0)
    (a := a) (b := 1 - 0.478 / s) (by simpa using hL) hL.le
  simp only [zero_mul, Real.exp_zero, mul_one, sub_zero, div_self hL.ne'] at h0
  have hid0 : L * (1 - 0.478 / s - 1) = -0.478 * L / s := by ring
  rw [hid0] at h0
  have h1 := integral_density_exponential (L := L) (D := 4 * z)
    (a := a) (b := 1 - 0.478 / s) hk hL.le
  have he : (L - 4 * z) * (1 - 0.478 / s - 1) ≤ -0.478 * L / s + 2.104 := by
    apply (mul_le_mul_iff_left₀ hs).mp
    field_simp
    nlinarith
  have hexp : Real.exp ((L - 4 * z) * (1 - 0.478 / s - 1)) ≤
      9 * Real.exp (-0.478 * L / s) := by
    calc
      _ ≤ Real.exp (-0.478 * L / s + 2.104) := Real.exp_le_exp.mpr he
      _ = Real.exp (-0.478 * L / s) * Real.exp 2.104 := Real.exp_add _ _
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left exp_density_shift_le
          (Real.exp_pos (-0.478 * L / s)).le
  have h1 := h1.trans (mul_le_mul hfrac hexp (Real.exp_pos _).le (by norm_num))
  have hi0 : IntervalIntegrable (fun alpha => L * Real.exp (L * (alpha - 1)))
      volume a (1 - 0.478 / s) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun alpha => L * Real.exp (L * (alpha - 1)) *
      Real.exp (4 * z * (1 - alpha))) volume a (1 - 0.478 / s) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hid (alpha : ℝ) :
      L * Real.exp (L * (alpha - 1)) *
        (16541 * z ^ 6 + 24200 * z ^ 6 * Real.exp (4 * z * (1 - alpha))) =
      (16541 * z ^ 6) * (L * Real.exp (L * (alpha - 1))) +
        (24200 * z ^ 6) * (L * Real.exp (L * (alpha - 1)) *
          Real.exp (4 * z * (1 - alpha))) := by ring
  simp_rw [hid]
  rw [intervalIntegral.integral_add (hi0.const_mul _) (hi1.const_mul _)]
  have hp := add_le_add
    (mul_le_mul_of_nonneg_left h0 (by positivity : 0 ≤ 16541 * z ^ 6))
    (mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 24200 * z ^ 6))
  have hE : 0 ≤ z ^ 6 * Real.exp (-0.478 * L / s) := by positivity
  simp only [intervalIntegral.integral_const_mul] at hp ⊢
  nlinarith only [hp, hE]

theorem source_density_integral_bound {q : ℕ} (hq : 0 < q) {X y s a : ℝ}
    (hX : 1 < X) (hy : 1 ≤ y) (hs : 0 < s)
    (hz : 36 ≤ Real.log ((q : ℝ) * y))
    (hzs : Real.log ((q : ℝ) * y) ≤ (11 / 10) * s)
    (hgap : 4 * Real.log ((q : ℝ) * y) ≤ Real.log X / 10)
    (hab : a ≤ 1 - 0.478 / s) :
    (∫ alpha in a..(1 - 0.478 / s), betaKernel X alpha * sourceDensity q y alpha) ≤
      (10 / 9) * (16541 + 9 * 24200) *
        Real.log ((q : ℝ) * y) ^ 6 * Real.exp (-0.478 * Real.log X / s) := by
  have hX0 : 0 < X := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hy0 : 0 < y := by linarith
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  have hly : Real.log y ≤ Real.log ((q : ℝ) * y) := by
    apply Real.log_le_log hy0
    nlinarith
  have hc : 17102 + 254231 / Real.log ((q : ℝ) * y) ≤ 24200 := by
    have hd : 254231 / Real.log ((q : ℝ) * y) ≤ 254231 / 36 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz
    linarith
  have hL := Real.log_pos hX
  have hid (alpha : ℝ) : betaKernel X alpha =
      Real.log X * Real.exp (Real.log X * (alpha - 1)) := by
    unfold betaKernel
    rw [Real.rpow_def_of_pos hX0]
    ring
  calc
    _ ≤ ∫ alpha in a..(1 - 0.478 / s),
        Real.log X * Real.exp (Real.log X * (alpha - 1)) *
          (16541 * Real.log ((q : ℝ) * y) ^ 6 +
            24200 * Real.log ((q : ℝ) * y) ^ 6 *
              Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha))) := by
      apply intervalIntegral.integral_mono_on hab
        (((betaKernel_continuous hX0).mul (sourceDensity_continuous hq hy0 (by linarith))).intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _)
      intro alpha halpha
      have ha : alpha ≤ 1 := by
        have hd : 0 ≤ 0.478 / s := by positivity
        linarith [halpha.2]
      have hd := density_power_envelope hq hy (by linarith) ha
      have hp := pow_le_pow_left₀ hl hly 6
      have hh := add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 16541))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc
            (pow_nonneg (show 0 ≤ Real.log ((q : ℝ) * y) by linarith) 6))
          (Real.exp_pos (4 * Real.log ((q : ℝ) * y) * (1 - alpha))).le)
      dsimp only [Pi.mul_apply]
      rw [hid]
      exact mul_le_mul_of_nonneg_left (hd.trans hh) (by positivity)
    _ ≤ _ := integrated_density_envelope hL hs (by linarith) hzs hgap

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
