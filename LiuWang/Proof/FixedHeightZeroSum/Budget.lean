import LiuWang.Proof.FixedHeightZeroSum.Transport
import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.LowBudget

/-!
# 固定高度运输与高实部化的数值支付

不改变旧低零点生产者的 `0.00001`；用 `L^96 ≤ N` 重新支付。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.LocalAnalyticBounds LiuWang.Proof.NonSymmetricContour

namespace LiuWang.Proof.FixedHeightZeroSum

theorem transport_cost_le_budget {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {t : Real}
    (htlo : sourceWindowLower N ≤ t) :
    (2 * 1.7769 * Real.log ((q : Real) * sourceT N)) *
        ((t + 2.5) / (sourceT N - 1)) ≤
      0.00015 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hT0 := sourceT_pos hN
  have hTbig : 10001 ≤ sourceT N :=
    (by norm_num : (10001 : Real) ≤ 2000 ^ (15 : Nat)).trans (sourceT_large hN)
  have hTm0 : 0 < sourceT N - 1 := by linarith
  have htT := sourceT_lt_real_endpoint hN htlo
  have ht0 : 0 < t := hT0.trans htT
  have htbig : 25000 ≤ t := by
    have hh : 25000 ≤ sourceT N :=
      (by norm_num : (25000 : Real) ≤ 2000 ^ (15 : Nat)).trans (sourceT_large hN)
    linarith
  have hc : t + 2.5 ≤ 1.0001 * t := by linarith
  have hratio : sourceT N / (sourceT N - 1) ≤ 1.0001 := by
    apply (div_le_iff₀ (by linarith : 0 < sourceT N - 1)).mpr
    linarith
  have hden : t / (sourceT N - 1) ≤ 1.0001 * (t / sourceT N) := by
    have hh := mul_le_mul_of_nonneg_right hratio (show 0 ≤ t / sourceT N by positivity)
    convert hh using 1 <;> first | rfl | field_simp
  have hkernel : (t + 2.5) / (sourceT N - 1) ≤ 1.0001 ^ (2 : Nat) * (t / sourceT N) := by
    calc
      _ ≤ (1.0001 * t) / (sourceT N - 1) :=
        div_le_div_of_nonneg_right hc (by linarith)
      _ = 1.0001 * (t / (sourceT N - 1)) := by ring
      _ ≤ 1.0001 * (1.0001 * (t / sourceT N)) :=
        mul_le_mul_of_nonneg_left hden (by norm_num)
      _ = _ := by ring
  obtain ⟨hlog0, hlog⟩ := source_log_qT_bounds hN hq hqUpper
  have hcoeff : (2 * 1.7769 * (21 / 250 : Real) * 1.0001 ^ (2 : Nat)) * sourceL N ≤
      0.00015 * sourceL N ^ (2 : Nat) := by
    have hh := mul_le_mul_of_nonneg_right hL hL0.le
    nlinarith
  calc
    _ ≤ (2 * 1.7769 * ((21 / 250 : Real) * sourceL N)) *
        (1.0001 ^ (2 : Nat) * (t / sourceT N)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num)) hkernel
        (by positivity) (by positivity)
    _ = ((2 * 1.7769 * (21 / 250 : Real) * 1.0001 ^ (2 : Nat)) * sourceL N) *
        (t / sourceT N) := by ring
    _ ≤ (0.00015 * sourceL N ^ (2 : Nat)) * (t / sourceT N) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring

theorem source_sqrt_endpoint_ge_hundred_million_power {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {t : Real}
    (htlo : sourceWindowLower N ≤ t) :
    100000000 * sourceL N ^ (44 : Nat) ≤ Real.sqrt t := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have ht0 : 0 < t := (sourceT_pos hN).trans (sourceT_lt_real_endpoint hN htlo)
  have hc : (10000000000000000000 : Real) ≤ sourceL N ^ (8 : Nat) := by
    calc
      _ ≤ (2000 : Real) ^ (8 : Nat) := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hL _
  have hp : 1000 * (100000000 * sourceL N ^ (44 : Nat)) ^ 2 ≤ (N : Real) := by
    calc
      _ = 10000000000000000000 * sourceL N ^ (88 : Nat) := by ring
      _ ≤ sourceL N ^ (8 : Nat) * sourceL N ^ (88 : Nat) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = sourceL N ^ (96 : Nat) := by ring
      _ ≤ Real.exp (sourceL N) := LeftVertical.pow_ninety_six_le_exp hL
      _ = (N : Real) := exp_sourceL (nat_pos_of_exp_le hN)
  change (N : Real) / 1000 ≤ t at htlo
  have hs : (100000000 * sourceL N ^ (44 : Nat)) ^ 2 ≤ t := by linarith
  nlinarith [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t]

theorem low_and_center_cost_le_budget {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {t : Real}
    (htlo : sourceWindowLower N ≤ t) :
    (2 * Real.sqrt t + 5) * (sourceT N ^ (2 : Nat) + 4) *
        (Real.log q / 2 + 15 / 2) ≤
      0.000001 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hT0 := sourceT_pos hN
  have hT1 : 1 ≤ sourceT N := one_le_pow₀ (one_le_sourceL hN)
  have ht0 : 0 < t := hT0.trans (sourceT_lt_real_endpoint hN htlo)
  have hq0 : (0 : Real) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqlog : Real.log q ≤ 6 * Real.log (sourceL N) := by
    have h := Real.log_le_log hq0 hqUpper
    change Real.log q ≤ Real.log (sourceL N ^ (6 : Nat)) at h
    simpa [Real.log_pow] using h
  have hlog : Real.log q / 2 + 15 / 2 ≤ sourceL N := by
    linarith [log_le_div_250 hL]
  have hlog0 : 0 ≤ Real.log q / 2 + 15 / 2 := by
    linarith [Real.log_nonneg hq1]
  have hheight : sourceT N ^ (2 : Nat) + 4 ≤ 5 * sourceT N ^ (2 : Nat) := by
    nlinarith
  have hsqrt := source_sqrt_endpoint_ge_hundred_million_power hN htlo
  have hsqrt1 : 1 ≤ Real.sqrt t := by
    have hp : 1 ≤ sourceL N ^ (44 : Nat) := one_le_pow₀ (one_le_sourceL hN)
    linarith
  have hcoarse : (2 * Real.sqrt t + 5) * (sourceT N ^ (2 : Nat) + 4) *
      (Real.log q / 2 + 15 / 2) ≤
      35 * Real.sqrt t * sourceT N ^ (2 : Nat) * sourceL N := by
    calc
      _ ≤ (7 * Real.sqrt t) * (5 * sourceT N ^ (2 : Nat)) * sourceL N :=
        mul_le_mul (mul_le_mul (by linarith) hheight (by positivity) (by positivity))
          hlog hlog0 (by positivity)
      _ = _ := by ring
  have hpay : 35 * sourceT N ^ (3 : Nat) ≤ 0.000001 * Real.sqrt t * sourceL N := by
    have hh := mul_le_mul_of_nonneg_right hsqrt hL0.le
    have heq : sourceL N ^ (44 : Nat) * sourceL N = sourceT N ^ (3 : Nat) := by
      unfold sourceT
      ring
    have hh' : 100000000 * sourceT N ^ (3 : Nat) ≤ Real.sqrt t * sourceL N := by
      calc
        _ = (100000000 * sourceL N ^ (44 : Nat)) * sourceL N := by rw [mul_assoc, heq]
        _ ≤ _ := hh
    nlinarith [pow_nonneg hT0.le 3]
  apply hcoarse.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hT0).mpr
  calc
    _ = (35 * sourceT N ^ (3 : Nat)) * (Real.sqrt t * sourceL N) := by ring
    _ ≤ (0.000001 * Real.sqrt t * sourceL N) * (Real.sqrt t * sourceL N) :=
      mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = 0.000001 * (Real.sqrt t) ^ 2 * sourceL N ^ (2 : Nat) := by ring
    _ = _ := by rw [Real.sq_sqrt ht0.le]

end LiuWang.Proof.FixedHeightZeroSum
