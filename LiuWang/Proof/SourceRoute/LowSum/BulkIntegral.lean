import LiuWang.Proof.SourceRoute.LowSum.PartialSummation

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.LowSum

theorem log_window_bounds : -7 ≤ Real.log (0.001 : ℝ) ∧ Real.log (0.001 : ℝ) ≤ -6 := by
  have hlo : 6 ≤ Real.log (1000 : ℝ) := by
    apply (Real.le_log_iff_exp_le (by norm_num)).mpr
    calc
      Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.7182818286 : ℝ) ^ 6 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
      _ ≤ _ := by norm_num
  have hhi : Real.log (1000 : ℝ) ≤ 7 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    calc
      (1000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 7 := by norm_num
      _ ≤ Real.exp 1 ^ 7 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 7
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  rw [show (0.001 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, Real.log_inv]
  constructor <;> linarith

theorem coefficient_half_upper : coefficient (1 / 2) ≤ 1.93676 := by
  have hp : 0 ≤ (0.001 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hs : ((0.001 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = 0.001 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  dsimp [coefficient]
  nlinarith

theorem coefficient_098_bounds : 1.0192 ≤ coefficient 0.98 ∧ coefficient 0.98 ≤ 1.0193 := by
  have hid : (0.001 : ℝ) ^ (0.98 : ℝ) =
      0.001 * Real.exp (-0.02 * Real.log (0.001 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num),
      show (0.001 : ℝ) = Real.exp (Real.log (0.001 : ℝ)) from (Real.exp_log (by norm_num)).symm,
      ← Real.exp_add]
    congr 1
    rw [Real.log_exp]
    ring
  have helo : 1.12 ≤ Real.exp (-0.02 * Real.log (0.001 : ℝ)) :=
    le_trans (by linarith [log_window_bounds.2]) (Real.add_one_le_exp _)
  have hehi : Real.exp (-0.02 * Real.log (0.001 : ℝ)) ≤ (2.14 : ℝ) / 1.86 := by
    apply (Real.exp_le_exp.mpr (show -0.02 * Real.log (0.001 : ℝ) ≤ 0.14 by
      linarith [log_window_bounds.1])).trans
    simpa only [show (2 : ℝ) + 0.14 = 2.14 by norm_num,
      show (2 : ℝ) - 0.14 = 1.86 by norm_num] using Real.exp_le_two_add_div_two_sub
      (by norm_num : (0 : ℝ) ≤ 0.14) (by norm_num : (0.14 : ℝ) < 2)
  dsimp [coefficient]
  rw [hid]
  constructor
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 0.98)).mpr
    linarith
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.98)).mpr
    linarith

theorem original_bulk_curly_bound {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0.98 ≤ b) :
    weight N (1 / 2) + (∫ alpha in (1 / 2 : ℝ)..b, kernel N alpha) ≤
      0.9176 * (N : ℝ) ^ (-1 / 50 : ℝ) + 1.0193 * (N : ℝ) ^ (b - 1) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (kernel_integrable hN (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 0.98))
    (kernel_integrable hN (by norm_num) hb)]
  have h1 := integral_kernel_le_endpoint_difference hN
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 0.98)
  have h2 := integral_kernel_le_endpoint_difference hN (by norm_num : (0 : ℝ) < 0.98) hb
  have hp : 0 ≤ (N : ℝ) ^ (-1 / 50 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hq : 0 ≤ (N : ℝ) ^ (b - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc : coefficient (1 / 2) - coefficient 0.98 ≤ 0.9176 := by
    linarith [coefficient_half_upper, coefficient_098_bounds.1]
  have hm1 := mul_le_mul_of_nonneg_right hc hp
  have hm2 := mul_le_mul_of_nonneg_right coefficient_098_bounds.2 hq
  change coefficient (1 / 2) * (N : ℝ) ^ ((1 / 2 : ℝ) - 1) + _ ≤ _
  norm_num only [show (0.98 : ℝ) - 1 = -1 / 50 by norm_num] at h1 h2
  linarith

theorem original_log_seed : Real.log (3.36 * (3100 : ℝ) ^ 3) ≤ 25.32942 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.32942) 8
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 25
  calc
    _ ≤ (2.7182818283 : ℝ) ^ 25 *
        (∑ i ∈ Finset.range 8, (0.32942 : ℝ) ^ i / i.factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1 ^ 25 * Real.exp 0.32942 :=
      mul_le_mul hp hs (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem decay_with_original_log_seed {L c s E : ℝ} (hL : 3100 ≤ L)
    (hc : 0.1 ≤ c) (hs0 : 0 ≤ s) (hs1 : s ≤ 60)
    (hseed : s * 25.32942 ≤ 3100 * c) (hE : Real.exp (-s) ≤ E) :
    Real.exp (-c * L / Real.log (3.36 * L ^ 3)) ≤ E * (3100 / L) ^ 5 := by
  let z := Real.log (L / 3100)
  have hp : 0 < L := by linarith
  have hz : 0 ≤ z := Real.log_nonneg (by linarith)
  have he : Real.exp z = L / 3100 := Real.exp_log (by positivity)
  have hquad := Real.quadratic_le_exp_of_nonneg hz
  rw [he] at hquad
  have hlo := (log_scale_bounds hL).1
  have hhi : Real.log (3.36 * L ^ 3) ≤ 25.32942 + 3 * z := by
    have hid : Real.log (3.36 * L ^ 3) =
        Real.log (3.36 * (3100 : ℝ) ^ 3) + 3 * z := by
      dsimp [z]
      rw [Real.log_mul (by norm_num) (pow_pos hp 3).ne',
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
        Real.log_div hp.ne' (by norm_num)]
      ring
    rw [hid]
    linarith [original_log_seed]
  have hprod := mul_le_mul_of_nonneg_left hhi (show 0 ≤ s + 5 * z by positivity)
  have hcprod := mul_nonneg (show 0 ≤ c - 0.1 by linarith) (show 0 ≤ L - 3100 by linarith)
  have hsprod := mul_nonneg (show 0 ≤ 60 - s by linarith) hz
  have hgap : (s + 5 * z) * Real.log (3.36 * L ^ 3) ≤ c * L := by
    nlinarith [sq_nonneg z]
  have hquot : s + 5 * z ≤ c * L / Real.log (3.36 * L ^ 3) :=
    (le_div_iff₀ (by linarith)).mpr hgap
  calc
    _ ≤ Real.exp (-s - 5 * z) := Real.exp_le_exp.mpr (by rw [neg_mul, neg_div]; linarith)
    _ = Real.exp (-s) * (3100 / L) ^ 5 := by
      have he5 : Real.exp (5 * z) = Real.exp z ^ 5 := by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul z 5
      rw [Real.exp_sub, he5, he]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hE (by positivity)

theorem exp_neg_original_bulk_seed : Real.exp (-58.5011 : ℝ) ≤ 3.9201e-26 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.5011) 9
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 58
  have he : (1 / (3.9201e-26) : ℝ) ≤ Real.exp 58.5011 := by
    calc
      _ ≤ (2.7182818283 : ℝ) ^ 58 *
          (∑ i ∈ Finset.range 9, (0.5011 : ℝ) ^ i / i.factorial) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1 ^ 58 * Real.exp 0.5011 :=
        mul_le_mul hp hs (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / (3.9201e-26)) he
  simpa only [Real.exp_neg, one_div, inv_inv] using h

theorem exp_neg_62 : Real.exp (-62 : ℝ) ≤ 1.186e-27 := by
  have he : (1 / (1.186e-27) : ℝ) ≤ Real.exp 62 := by
    calc
      _ ≤ (2.7182818283 : ℝ) ^ 62 := by norm_num
      _ ≤ Real.exp 1 ^ 62 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 62
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / (1.186e-27)) he
  simpa only [Real.exp_neg, one_div, inv_inv] using h

theorem exp_neg_fiftieth_decay {L : ℝ} (hL : 3100 ≤ L) :
    Real.exp (-L / 50) ≤ 1.186e-27 * (3100 / L) ^ 5 := by
  have hp : 0 < L := by linarith
  have hz := Real.log_le_sub_one_of_pos (show 0 < L / 3100 by positivity)
  have hgap : 62 + 5 * Real.log (L / 3100) ≤ L / 50 := by linarith
  calc
    _ ≤ Real.exp (-62 - 5 * Real.log (L / 3100)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-62) * (3100 / L) ^ 5 := by
      have he5 : Real.exp (5 * Real.log (L / 3100)) = (L / 3100) ^ 5 := by
        rw [show (5 : ℝ) = (5 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log (by positivity)]
      rw [Real.exp_sub, he5]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right exp_neg_62 (by positivity)

theorem original_bulk_integral_numeric {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (8.82 * sourceP N * Real.log (sourceP N)) *
      (weight N (1 / 2) + ∫ alpha in (1 / 2 : ℝ)..bulkCap N, kernel N alpha) ≤
        8.1e-10 / sourceL N := by
  let L := sourceL N
  have hL : 3100 ≤ L := sourceL_ge_3100 hN
  have hp : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hb : 0.98 ≤ bulkCap N := by
    have hl : 25 ≤ Real.log (lowScale N) := (log_scale_bounds hL).1
    have hd : 0.478 / Real.log (lowScale N) ≤ 0.02 :=
      (div_le_iff₀ (by linarith)).mpr (by linarith)
    dsimp [bulkCap]
    linarith
  have hcurly := original_bulk_curly_bound (nat_pos_of_exp_le hN) hb
  have hid1 : (N : ℝ) ^ (-1 / 50 : ℝ) = Real.exp (-L / 50) := by
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (nat_pos_of_exp_le hN))]
    congr 1
    dsimp [L, sourceL]
    ring
  have hid2 : (N : ℝ) ^ (bulkCap N - 1) =
      Real.exp (-0.478 * L / Real.log (3.36 * L ^ 3)) := by
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (nat_pos_of_exp_le hN))]
    congr 1
    dsimp [bulkCap, lowScale, sourceP, L, sourceL]
    ring
  rw [hid1, hid2] at hcurly
  have hd1 := exp_neg_fiftieth_decay hL
  have hd2 := decay_with_original_log_seed hL (c := 0.478) (s := 58.5011)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) exp_neg_original_bulk_seed
  have hpaid : weight N (1 / 2) + (∫ alpha in (1 / 2 : ℝ)..bulkCap N, kernel N alpha) ≤
      (0.9176 * 1.186e-27 + 1.0193 * 3.9201e-26) * (3100 / L) ^ 5 := by
    nlinarith
  have hm : 0 ≤ 8.82 * sourceP N * Real.log (sourceP N) := by
    change 0 ≤ 8.82 * L ^ 3 * Real.log (L ^ 3)
    rw [Real.log_pow]
    positivity
  apply (mul_le_mul_of_nonneg_left hpaid hm).trans
  let K : ℝ := 26.46 * (0.9176 * 1.186e-27 + 1.0193 * 3.9201e-26) * 3100 ^ 5
  calc
    _ = K * (Real.log L / L) / L := by
      change (8.82 * L ^ 3 * Real.log (L ^ 3)) * _ = _
      rw [Real.log_pow]
      dsimp [K]
      field_simp
      ring
    _ ≤ K * (8.04 / 3100) / L :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (log_over_self_bound hL) (by dsimp [K]; positivity)) hp.le
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num [K]) hp.le

end LiuWang.Proof.SourceRoute.LowSum
