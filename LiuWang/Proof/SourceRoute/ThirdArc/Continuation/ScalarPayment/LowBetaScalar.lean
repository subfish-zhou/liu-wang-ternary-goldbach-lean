import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowStrip
import LiuWang.Proof.WeightedLowZeros.Continuation.LogBudget

/-! Global L-decay and fixed rational certification for the original (5.23) price. -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment

theorem lowCoefficient_half_le : lowCoefficient (1 / 2) ≤ 1.937 := by
  have hs : (0.0315 : ℝ) ≤ Real.sqrt 0.001 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  unfold lowCoefficient
  rw [← Real.sqrt_eq_rpow]
  linarith

theorem fifth_power_decay {L : ℝ} (hL : 3100 ≤ L) :
    L ^ 5 * Real.exp (-L / 60) ≤ 3100 ^ 5 * Real.exp (-(3100 : ℝ) / 60) := by
  let r := L / 3100
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have he : r ≤ Real.exp (r - 1) := by linarith [Real.add_one_le_exp (r - 1)]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ r) he 5
  have hLr : L = 3100 * r := by dsimp [r]; ring
  calc
    _ = 3100 ^ 5 * r ^ 5 * Real.exp (-(3100 * r) / 60) := by
      conv_lhs => rw [hLr]
      ring
    _ ≤ 3100 ^ 5 * Real.exp (r - 1) ^ 5 * Real.exp (-(3100 * r) / 60) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (Real.exp_pos _).le
    _ = 3100 ^ 5 * Real.exp (5 * (r - 1) - 3100 * r / 60) := by
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)

theorem low_beta_endpoint_certificate :
    (1.937 * (10004 * 6 * 8.04 + 76100) * 3100 ^ 4 : ℝ) *
      Real.exp (-(3100 : ℝ) / 60) ≤ 0.00365 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 51
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have he := mul_le_mul hp ht (by norm_num) (by positivity)
  rw [← Real.exp_nat_mul, ← Real.exp_add] at he
  norm_num at he
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 0.00365)
  norm_num at h ⊢
  linarith

theorem low_beta_global_decay {L : ℝ} (hL : 3100 ≤ L) :
    1.937 * L ^ 4 * (10004 * (6 * Real.log L) + 76100) * Real.exp (-L / 60) ≤
      0.00365 := by
  have hpos : 0 < L := by linarith
  have hlog := WeightedLowZeros.Continuation.log_over_self_bound hL
  have hlog' : Real.log L ≤ 8.04 * (L / 3100) := by
    have h := (div_le_iff₀ hpos).mp hlog
    nlinarith
  have ha : 10004 * (6 * Real.log L) + 76100 ≤
      (10004 * 6 * 8.04 + 76100) * (L / 3100) := by nlinarith
  calc
    _ ≤ 1.937 * L ^ 4 * ((10004 * 6 * 8.04 + 76100) * (L / 3100)) *
        Real.exp (-L / 60) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by positivity)) (Real.exp_pos _).le
    _ = (1.937 * (10004 * 6 * 8.04 + 76100) / 3100) * (L ^ 5 * Real.exp (-L / 60)) := by ring
    _ ≤ (1.937 * (10004 * 6 * 8.04 + 76100) / 3100) *
        (3100 ^ 5 * Real.exp (-(3100 : ℝ) / 60)) :=
      mul_le_mul_of_nonneg_left (fifth_power_decay hL) (by positivity)
    _ ≤ _ := by convert low_beta_endpoint_certificate using 1; ring

theorem low_beta_scalar_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    (N : ℝ) * Real.sqrt q * lowCoefficient (1 / 2) *
        (10004 * Real.log q + 76100) * (N : ℝ) ^ (-1 / 60 : ℝ) ≤
      0.00365 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hqlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
  have hs : Real.sqrt (q : ℝ) ≤ sourceL N ^ 3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    change (q : ℝ) ≤ sourceL N ^ 6 at hq1
    nlinarith only [hq1]
  have hlog : Real.log (q : ℝ) ≤ 6 * Real.log (sourceL N) := by
    have h := Real.log_le_log hqR hq1
    simpa only [sourceP1, Real.log_pow, Nat.cast_ofNat] using h
  have he : (N : ℝ) ^ (-1 / 60 : ℝ) = Real.exp (-sourceL N / 60) := by
    rw [Real.rpow_def_of_pos (natCast_pos_of_exp_le hN), sourceL]
    congr 1
    ring
  rw [he]
  apply (le_div_iff₀ hLp).mpr
  have hb : Real.sqrt q * lowCoefficient (1 / 2) * (10004 * Real.log q + 76100) ≤
      sourceL N ^ 3 * 1.937 * (10004 * (6 * Real.log (sourceL N)) + 76100) :=
    mul_le_mul (mul_le_mul hs lowCoefficient_half_le (lowCoefficient_nonneg (by norm_num))
      (by positivity)) (by linarith) (by positivity) (by positivity)
  have h := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (N : ℝ) * sourceL N * Real.exp (-sourceL N / 60) by positivity)
  have hpaid := mul_le_mul_of_nonneg_left (low_beta_global_decay hL) (Nat.cast_nonneg (α := ℝ) N)
  nlinarith only [h, hpaid]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment
