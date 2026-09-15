import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityLogs
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowBetaScalar

/-! The original (5.30) and (5.40) low-beta scalar integrals, without density assumptions. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

theorem sixth_power_decay {L : ℝ} (hL : 3100 ≤ L) :
    (L / 3100) ^ 6 * Real.exp (-L / 60) ≤ Real.exp (-(3100 : ℝ) / 60) := by
  let r := L / 3100
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have he : r ≤ Real.exp (r - 1) := by linarith [Real.add_one_le_exp (r - 1)]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ r) he 6
  have hLr : L = 3100 * r := by dsimp [r]; ring
  calc
    _ ≤ Real.exp (r - 1) ^ 6 * Real.exp (-L / 60) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (6 * (r - 1) - L / 60) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by rw [hLr]; linarith)

theorem middle_base_factor : (0.001 : ℝ) ^ (-1 / 60 : ℝ) ≤ 1.2 := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (60 : ℕ) ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 0.001)]
  norm_num

theorem middle_height_log_global {L : ℝ} (hL : 3100 ≤ L) :
    Real.log (10 * Real.pi * L ^ 7) ≤ 60 * (L / 3100) := by
  have hL0 : 0 < L := by linarith
  have hlog : Real.log (10 * Real.pi) ≤ 3.5 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.718)
      (by linarith [Real.exp_one_gt_d9] : (2.718 : ℝ) ≤ Real.exp 1) 3
    rw [← Real.exp_nat_mul] at h
    simp only [Nat.cast_ofNat, mul_one] at h
    have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.5)
    have hh := mul_le_mul h he (by norm_num) (Real.exp_pos _).le
    rw [← Real.exp_add] at hh
    norm_num at hh ⊢
    nlinarith [Real.pi_lt_d2]
  have hu := (div_le_iff₀ hL0).mp (log_over_self_bound hL)
  rw [Real.log_mul (by positivity : 10 * Real.pi ≠ 0) (pow_ne_zero _ hL0.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem middle_power_global {L : ℝ} (hL : 3100 ≤ L) :
    L ^ (3.5 : ℝ) ≤ (3100 ^ 3 * 56 : ℝ) * (L / 3100) ^ 4 := by
  have hr : (1 : ℝ) ≤ L / 3100 := by linarith
  have hs : Real.sqrt (3100 : ℝ) ≤ 56 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hp : (3100 : ℝ) ^ (3.5 : ℝ) ≤ (3100 : ℝ) ^ 3 * 56 := by
    rw [show (3.5 : ℝ) = (3 : ℕ) + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left hs (by norm_num)
  have he := Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (3.5 : ℝ) ≤ (4 : ℕ))
  rw [Real.rpow_natCast] at he
  calc
    _ = ((3100 : ℝ) * (L / 3100)) ^ (3.5 : ℝ) := by congr 1; ring
    _ = (3100 : ℝ) ^ (3.5 : ℝ) * (L / 3100) ^ (3.5 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ _ := mul_le_mul hp he (by positivity) (by norm_num)

theorem lower_beta_endpoint_prices :
    (80 * 1.2 * 60 * 56 * 3100 ^ 4 : ℝ) * Real.exp (-(3100 : ℝ) / 60) ≤ 0.0011 ∧
      (505 * 8.04 ^ 2 * 3100 ^ 4 : ℝ) * Real.exp (-(3100 : ℝ) / 60) ≤ 0.00012 := by
  have h := low_beta_endpoint_certificate
  have he := (Real.exp_pos (-(3100 : ℝ) / 60)).le
  constructor <;> nlinarith only [h, he]

theorem equation_5_30_scalar {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    80 * N * sourceL N ^ (3.5 : ℝ) * Real.log (10 * Real.pi * sourceL N ^ 7) *
        (0.001 * N) ^ (-1 / 60 : ℝ) ≤ 0.0011 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hx := natCast_pos_of_exp_le hN
  have hlog0 : 0 ≤ Real.log (10 * Real.pi * sourceL N ^ 7) := by
    apply Real.log_nonneg
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (show 1 ≤ sourceL N by linarith) 7
    nlinarith [Real.pi_gt_three]
  have he : (N : ℝ) ^ (-1 / 60 : ℝ) = Real.exp (-sourceL N / 60) := by
    rw [Real.rpow_def_of_pos hx, sourceL]
    congr 1
    ring
  have hbase : (0.001 * N) ^ (-1 / 60 : ℝ) ≤ 1.2 * Real.exp (-sourceL N / 60) := by
    rw [Real.mul_rpow (by norm_num) hx.le, he]
    exact mul_le_mul_of_nonneg_right middle_base_factor (Real.exp_pos _).le
  have hp := mul_le_mul (middle_power_global hL) (middle_height_log_global hL)
    hlog0 (by positivity)
  have hp := mul_le_mul hp hbase (by positivity) (by positivity)
  have hp := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 80 * (N : ℝ) * sourceL N by positivity)
  have hd := mul_le_mul_of_nonneg_left (sixth_power_decay hL)
    (show 0 ≤ (N : ℝ) * (80 * 1.2 * 60 * 56 * 3100 ^ 4) by positivity)
  have hf := mul_le_mul_of_nonneg_left lower_beta_endpoint_prices.1 (Nat.cast_nonneg (α := ℝ) N)
  apply (le_div_iff₀ hL0).mpr
  nlinarith only [hp, hd, hf]

theorem high_lower_beta_scalar {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    505 * N * Real.sqrt q * Real.log (sourceL N) ^ 2 * (N : ℝ) ^ (-1 / 60 : ℝ) ≤
      0.00012 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hs : Real.sqrt (q : ℝ) ≤ sourceL N ^ 3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    change (q : ℝ) ≤ sourceL N ^ 6 at hq1
    nlinarith only [hq1]
  have hl : 0 ≤ Real.log (sourceL N) := Real.log_nonneg (by linarith)
  have hu := (div_le_iff₀ hL0).mp (log_over_self_bound hL)
  have hu : Real.log (sourceL N) ≤ 8.04 * (sourceL N / 3100) := by nlinarith
  have hp := mul_le_mul hs (pow_le_pow_left₀ hl hu 2) (sq_nonneg _) (by positivity)
  have he : (N : ℝ) ^ (-1 / 60 : ℝ) = Real.exp (-sourceL N / 60) := by
    rw [Real.rpow_def_of_pos (natCast_pos_of_exp_le hN), sourceL]
    congr 1
    ring
  rw [he]
  have hp := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 505 * (N : ℝ) * sourceL N * Real.exp (-sourceL N / 60) by positivity)
  have hd := mul_le_mul_of_nonneg_left (sixth_power_decay hL)
    (show 0 ≤ (N : ℝ) * (505 * 8.04 ^ 2 * 3100 ^ 4) by positivity)
  have hf := mul_le_mul_of_nonneg_left lower_beta_endpoint_prices.2 (Nat.cast_nonneg (α := ℝ) N)
  apply (le_div_iff₀ hL0).mpr
  nlinarith only [hp, hd, hf]

theorem lower_beta_integral_identity {X : ℝ} (hX : 0 < X) :
    X ^ (-1 / 2 : ℝ) + (∫ alpha in (1 / 2 : ℝ)..(59 / 60), betaKernel X alpha) =
      X ^ (-1 / 60 : ℝ) := by
  rw [integral_betaKernel hX]
  norm_num

theorem equation_5_30_integral {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    80 * N * sourceL N ^ (3.5 : ℝ) * Real.log (10 * Real.pi * sourceL N ^ 7) *
        ((0.001 * N) ^ (-1 / 2 : ℝ) +
          ∫ alpha in (1 / 2 : ℝ)..(59 / 60), betaKernel (0.001 * N) alpha) ≤
      0.0011 * (N : ℝ) / sourceL N := by
  rw [lower_beta_integral_identity (mul_pos (by norm_num) (natCast_pos_of_exp_le hN))]
  exact equation_5_30_scalar hN

theorem equation_5_40_low_integral {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    505 * N * Real.sqrt q * Real.log (sourceL N) ^ 2 *
        ((N : ℝ) ^ (-1 / 2 : ℝ) +
          ∫ alpha in (1 / 2 : ℝ)..(59 / 60), betaKernel N alpha) ≤
      0.00012 * (N : ℝ) / sourceL N := by
  rw [lower_beta_integral_identity (natCast_pos_of_exp_le hN)]
  exact high_lower_beta_scalar hN hq1

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
