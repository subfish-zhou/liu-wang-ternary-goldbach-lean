import LiuWang.Proof.SourceRoute.SecondArc.Continuation.GaussianPayment

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation

theorem low_alpha_bracket {x : ℝ} (hx : 0 < x) :
    x ^ (-1 / 2 : ℝ) + (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
      alphaKernel x alpha) = x ^ (-1 / 60 : ℝ) := by
  rw [integral_alphaKernel hx]
  norm_num

theorem fixed_low_alpha_exponential : Real.exp (-51.55 : ℝ) ≤ 0.000000000000000000000042 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos (51.55 : ℝ))).mpr
  have he : (2.718 : ℝ) ^ (51 : ℕ) * (1 + 0.55 + 0.55 ^ (2 : ℕ) / 2) ≤
      Real.exp (51.55 : ℝ) := by
    calc
      _ ≤ Real.exp 1 ^ (51 : ℕ) * Real.exp 0.55 :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num)
          (by linarith [Real.exp_one_gt_d9]) _)
          (by nlinarith [Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.55)])
          (by norm_num) (by positivity)
      _ = Real.exp 51.55 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  linarith

theorem low_alpha_scalar_payment {L : ℝ} (hL : 3100 ≤ L) :
    2 * Real.sqrt (10 / Real.pi) * L ^ (4 : ℕ) * Real.sqrt L *
      Real.log (10 * Real.pi * L ^ (10 : ℕ)) *
        Real.exp (-(L + Real.log 0.001) / 60) ≤ 0.000065 := by
  let t := L / 3100
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := by linarith
  have hLt : L = 3100 * t := by dsimp [t]; ring
  have hL0 : 0 < L := by linarith
  have hroot : Real.sqrt L ≤ 55.68 * t := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg (t - 1)]
  have hpi : Real.sqrt (10 / Real.pi) ≤ 1.785 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_d2]
  have hlog : Real.log (10 * Real.pi * L ^ (10 : ℕ)) ≤ 84 * t := by
    rw [Real.log_mul (by positivity : 10 * Real.pi ≠ 0) (by positivity), Real.log_pow]
    have hl : Real.log L = Real.log (3100 : ℝ) + Real.log t := by
      conv_lhs => rw [hLt]
      rw [Real.log_mul (by norm_num) ht0.ne']
    rw [hl]
    norm_num only [Nat.cast_ofNat]
    linarith [log_ten_pi_le_35, log_3100_bounds.2, Real.log_le_sub_one_of_pos ht0]
  have hH : 3093 * t ≤ L + Real.log (0.001 : ℝ) := by
    have hh := original_H_ge_scaling (L := (3100 : ℝ)) (by norm_num)
    have hs : scaling (3100 : ℝ) = 1 := by norm_num [scaling]
    rw [hs] at hh
    nlinarith
  have he : Real.exp (-(L + Real.log 0.001) / 60) ≤ Real.exp (-51.55 * t) :=
    Real.exp_le_exp.mpr (by linarith)
  have habs : t ^ (6 : ℕ) * Real.exp (-51.55 * t) ≤ Real.exp (-51.55 : ℝ) := by
    calc
      _ = Real.exp (6 * Real.log t + -51.55 * t) := by
        rw [Real.exp_add, show (6 : ℝ) = (6 : ℕ) by norm_num,
          Real.exp_nat_mul, Real.exp_log ht0]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Real.log_le_sub_one_of_pos ht0])
  have hlog0 : 0 ≤ Real.log (10 * Real.pi * L ^ (10 : ℕ)) := by
    apply Real.log_nonneg
    have hp : 1 ≤ L ^ (10 : ℕ) := one_le_pow₀ (by linarith : 1 ≤ L)
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ 2 * 1.785 * (3100 * t) ^ (4 : ℕ) * (55.68 * t) * (84 * t) *
        Real.exp (-51.55 * t) := by
      rw [← hLt]
      gcongr
    _ = (2 * 1.785 * 3100 ^ (4 : ℕ) * 55.68 * 84) *
        (t ^ (6 : ℕ) * Real.exp (-51.55 * t)) := by ring
    _ ≤ (2 * 1.785 * 3100 ^ (4 : ℕ) * 55.68 * 84) * Real.exp (-51.55 : ℝ) :=
      mul_le_mul_of_nonneg_left habs (by norm_num)
    _ ≤ (2 * 1.785 * 3100 ^ (4 : ℕ) * 55.68 * 84) * 0.000000000000000000000042 :=
      mul_le_mul_of_nonneg_left fixed_low_alpha_exponential (by norm_num)
    _ ≤ 0.000065 := by norm_num

theorem original_55_payment {L : ℝ} (hL : 3100 ≤ L) :
    (Real.exp L * 0.001) ^ (-1 / 60 : ℝ) *
      (2 * Real.sqrt (10 / Real.pi) * L ^ (3.5 : ℝ) *
        Real.log (10 * Real.pi * L ^ (10 : ℕ))) ≤ 0.000065 / L := by
  have hL0 : 0 < L := by linarith
  have hp : (Real.exp L * 0.001) ^ (-1 / 60 : ℝ) =
      Real.exp (-(L + Real.log 0.001) / 60) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (by positivity) (by norm_num),
      Real.log_exp]
    congr 1
    ring
  have hpow : L ^ (3.5 : ℝ) = L ^ (3 : ℕ) * Real.sqrt L := by
    rw [show (3.5 : ℝ) = (3 : ℕ) + (1 / 2 : ℝ) by norm_num,
      Real.rpow_add hL0, Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [hp, hpow]
  apply (le_div_iff₀ hL0).mpr
  nlinarith only [low_alpha_scalar_payment hL]

theorem original_55_bracket_payment {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ((0.001 * (N : ℝ)) ^ (-1 / 2 : ℝ) +
        ∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ), alphaKernel (0.001 * (N : ℝ)) alpha) *
      (2 * Real.sqrt (10 / Real.pi) * sourceL N ^ (3.5 : ℝ) *
        (q : ℝ) ^ (-0.5 : ℝ) * (Nat.totient q : ℝ) *
        Real.log (10 * Real.pi * sourceL N ^ (10 : ℕ))) ≤
      0.000065 * (q : ℝ) ^ (-0.5 : ℝ) * (Nat.totient q : ℝ) / sourceL N := by
  have hNp := natCast_pos_of_exp_le hN
  rw [low_alpha_bracket (by positivity : 0 < 0.001 * (N : ℝ))]
  have ht := original_55_payment (sourceL_ge_3100 hN)
  have hx : Real.exp (sourceL N) * 0.001 = 0.001 * (N : ℝ) := by
    unfold sourceL
    rw [Real.exp_log hNp]
    ring
  rw [hx] at ht
  have hm := mul_le_mul_of_nonneg_right ht
    (by positivity : 0 ≤ (q : ℝ) ^ (-0.5 : ℝ) * (Nat.totient q : ℝ))
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm

end LiuWang.Proof.SourceRoute.SecondArc.Continuation
