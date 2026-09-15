import LiuWang.Proof.SourceRoute.HighSum.SourceParameters
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Uniform certification of the original scalar endpoint bound (2.21)

This pays the published explicit expression, not the unprovided high-alpha
Theorem 7 comparison between that expression and the actual count.
-/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation

theorem log_3100_bounds : (8 : ℝ) ≤ Real.log 3100 ∧ Real.log 3100 ≤ 201 / 25 := by
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num)).mpr
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 68 / 25)) 8
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  · apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
      Real.exp_one_gt_d9.le 8
    rw [← Real.exp_nat_mul] at h
    norm_num only [Nat.cast_ofNat, mul_one] at h
    have ht : (26 / 25 : ℝ) ≤ Real.exp (1 / 25) := by
      linarith [Real.add_one_le_exp (1 / 25 : ℝ)]
    have hh := mul_le_mul h ht (by norm_num) (Real.exp_pos 8).le
    rw [← Real.exp_add] at hh
    norm_num at hh
    linarith

theorem original_log_linear {L : ℝ} (hL : 3100 ≤ L) :
    8 ≤ Real.log L ∧ Real.log L ≤ (201 / 25) * (L / 3100) := by
  have h0 : 0 < L := by linarith
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 3100) hL
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < L / 3100)
  rw [Real.log_div h0.ne' (by norm_num)] at h
  constructor <;> linarith [log_3100_bounds.1, log_3100_bounds.2]

theorem endpoint_root_certificates :
    (22 / 5 : ℝ) ≤ (3618 / 25 : ℝ) ^ (3 / 10 : ℝ) ∧
      (82 : ℝ) ≤ (3100 : ℝ) ^ (11 / 20 : ℝ) := by
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 10) (by norm_num) (by positivity)
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  · apply le_of_pow_le_pow_left₀ (n := 20) (by norm_num) (by positivity)
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num

theorem endpoint_log_power {L : ℝ} (hL : 3100 ≤ L) :
    (18 * Real.log L) ^ (57 / 10 : ℝ) ≤
      ((3618 / 25 : ℝ) ^ (6 : ℕ) / (22 / 5)) * (L / 3100) ^ (6 : ℕ) := by
  have hlog := original_log_linear hL
  have hr : 1 ≤ L / 3100 := by linarith
  have hbase : (3618 / 25 : ℝ) ^ (57 / 10 : ℝ) ≤
      (3618 / 25 : ℝ) ^ (6 : ℕ) / (22 / 5) := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 22 / 5)).mpr
    calc
      _ ≤ (3618 / 25 : ℝ) ^ (57 / 10 : ℝ) *
          (3618 / 25 : ℝ) ^ (3 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left endpoint_root_certificates.1 (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; norm_num
  calc
    _ ≤ ((3618 / 25) * (L / 3100)) ^ (57 / 10 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    _ = (3618 / 25 : ℝ) ^ (57 / 10 : ℝ) * (L / 3100) ^ (57 / 10 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ _ := mul_le_mul hbase (by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num))
      (by positivity) (by positivity)

theorem endpoint_denominator {L : ℝ} (hL : 3100 ≤ L) :
    (3100 : ℝ) ^ (7 : ℕ) * 82 * (L / 3100) ^ (6 : ℕ) ≤ L ^ (151 / 20 : ℝ) := by
  have h0 : 0 < L := by linarith
  have hr : 82 ≤ L ^ (11 / 20 : ℝ) :=
    endpoint_root_certificates.2.trans
      (Real.rpow_le_rpow (by norm_num) hL (by norm_num))
  calc
    _ = L ^ (6 : ℕ) * (3100 * 82) := by ring
    _ ≤ L ^ (6 : ℕ) * (L * L ^ (11 / 20 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hL hr (by norm_num) h0.le) (by positivity)
    _ = _ := by
      have he : L * L ^ (11 / 20 : ℝ) = L ^ (31 / 20 : ℝ) := by
        calc
          _ = L ^ (1 : ℝ) * L ^ (11 / 20 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add h0]; norm_num
      rw [he, ← Real.rpow_natCast, ← Real.rpow_add h0]
      norm_num

theorem endpoint_first_normalized {L : ℝ} (hL : 3100 ≤ L) :
    (17102 + 254231 / (18 * Real.log L)) * (18 * Real.log L) ^ (57 / 10 : ℝ) /
      L ^ (151 / 20 : ℝ) ≤ 179 / 1000000000000 := by
  have h0 : 0 < L := by linarith
  have hlog := original_log_linear hL
  have hc : 17102 + 254231 / (18 * Real.log L) ≤ 17102 + 254231 / (144 : ℝ) := by
    gcongr
    linarith
  have hn := mul_le_mul hc (endpoint_log_power hL)
    (Real.rpow_nonneg (by linarith) _) (by norm_num)
  have hd := endpoint_denominator hL
  apply (div_le_iff₀ (Real.rpow_pos_of_pos h0 _)).mpr
  have hpay : (17102 + 254231 / (144 : ℝ)) *
      ((3618 / 25 : ℝ) ^ (6 : ℕ) / (22 / 5)) ≤
      (179 / 1000000000000 : ℝ) * ((3100 : ℝ) ^ (7 : ℕ) * 82) := by norm_num
  have hpay' := mul_le_mul_of_nonneg_right hpay (by positivity : 0 ≤ (L / 3100) ^ (6 : ℕ))
  have hd' := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 179 / 1000000000000)
  nlinarith only [hn, hpay', hd']

theorem endpoint_second_normalized {L : ℝ} (hL : 3100 ≤ L) :
    16541 * (15 * Real.log L) ^ (6 : ℕ) / L ^ (11 : ℕ) ≤
      1 / 1000000000000 := by
  have h0 : 0 < L := by linarith
  have hlog := original_log_linear hL
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 15 * Real.log L)
    (show 15 * Real.log L ≤ (603 / 5) * (L / 3100) by linarith) 6
  have hd := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 5
  have hpay : (16541 : ℝ) * (603 / 5) ^ (6 : ℕ) / 3100 ^ (6 : ℕ) ≤
      (1 / 1000000000000 : ℝ) * 3100 ^ (5 : ℕ) := by norm_num
  have hm := mul_le_mul_of_nonneg_right
    (hpay.trans (mul_le_mul_of_nonneg_left hd (by norm_num))) (pow_nonneg h0.le 6)
  apply (div_le_iff₀ (pow_pos h0 _)).mpr
  calc
    _ ≤ 16541 * ((603 / 5) * (L / 3100)) ^ (6 : ℕ) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ _ := by nlinarith only [hm]

theorem original_source21_scalar {L : ℝ} (hL : 3100 ≤ L) :
    (17102 + 254231 / (18 * Real.log L)) * (18 * Real.log L) ^ (57 / 10 : ℝ) *
        L ^ ((69 : ℝ) / 20 - 15) +
      16541 / L ^ (15 : ℕ) * (15 * Real.log L) ^ (6 : ℕ) ≤
        (18 / 100000000000 : ℝ) / L ^ (4 : ℕ) := by
  have h0 : 0 < L := by linarith
  have he : L ^ ((69 : ℝ) / 20 - 15) * L ^ (4 : ℕ) =
      (L ^ (151 / 20 : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add h0, ← Real.rpow_neg h0.le]
    congr 1
    norm_num
  apply (le_div_iff₀ (pow_pos h0 _)).mpr
  have h1 := endpoint_first_normalized hL
  have h2 := endpoint_second_normalized hL
  calc
    _ = (17102 + 254231 / (18 * Real.log L)) * (18 * Real.log L) ^ (57 / 10 : ℝ) /
        L ^ (151 / 20 : ℝ) +
        16541 * (15 * Real.log L) ^ (6 : ℕ) / L ^ (11 : ℕ) := by
      rw [add_mul, mul_assoc, he]
      field_simp
    _ ≤ _ := by linarith

end LiuWang.Proof.SourceRoute.HighSum.Continuation
