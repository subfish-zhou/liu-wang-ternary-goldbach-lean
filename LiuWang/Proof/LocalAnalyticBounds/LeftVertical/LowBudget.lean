import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.LowZeros
import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Budget

/-!
# 大 N 下全部低实部居中零点贡献的支付

第四阶指数项给 `L^96 ≤ exp L`，足以吸收二次高度粗计数。
这只是实际居中有限和的估计，不是留数公式或去中心化公式。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical

theorem pow_ninety_six_le_exp {x : Real} (hx : 2000 ≤ x) :
    x ^ (96 : Nat) ≤ Real.exp x := by
  have hx0 : 0 ≤ x := by linarith
  have hfour := Real.pow_div_factorial_le_exp
    (x := x / 96) (by positivity) 4
  norm_num at hfour
  have hcube : (2000 : Real) ^ (3 : Nat) ≤ x ^ (3 : Nat) :=
    pow_le_pow_left₀ (by norm_num) hx _
  have hsmall : x ≤ Real.exp (x / 96) := by
    nlinarith [mul_le_mul_of_nonneg_right hcube hx0]
  have hp := pow_le_pow_left₀ hx0 hsmall 96
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  rwa [show (96 : Real) * (x / 96) = x by ring] at hp

theorem source_sqrt_endpoint_ge_large_power {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {t : Real}
    (htlo : sourceWindowLower N ≤ t) :
    2000000 * sourceL N ^ (44 : Nat) ≤ Real.sqrt t := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have ht0 : 0 < t := (sourceT_pos hN).trans (sourceT_lt_real_endpoint hN htlo)
  have hc : (4000000000000000 : Real) ≤ sourceL N ^ (8 : Nat) := by
    calc
      _ ≤ (2000 : Real) ^ (8 : Nat) := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hL _
  have hp : 1000 * (2000000 * sourceL N ^ (44 : Nat)) ^ 2 ≤ (N : Real) := by
    calc
      _ = 4000000000000000 * sourceL N ^ (88 : Nat) := by ring
      _ ≤ sourceL N ^ (8 : Nat) * sourceL N ^ (88 : Nat) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = sourceL N ^ (96 : Nat) := by ring
      _ ≤ Real.exp (sourceL N) := pow_ninety_six_le_exp hL
      _ = (N : Real) := exp_sourceL (nat_pos_of_exp_le hN)
  change (N : Real) / 1000 ≤ t at htlo
  have hs : (2000000 * sourceL N ^ (44 : Nat)) ^ 2 ≤ t := by linarith
  nlinarith [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t]

theorem lowZero_explicit_cost_le_small_budget {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {t : Real}
    (htlo : sourceWindowLower N ≤ t) :
    2 * Real.sqrt t * ((sourceT N + 1) ^ 2 + 4) * (Real.log q / 2 + 15 / 2) ≤
      (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat) := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hT0 := sourceT_pos hN
  have hT1 : 1 ≤ sourceT N := one_le_pow₀ (one_le_sourceL hN)
  have ht0 : 0 < t := hT0.trans (sourceT_lt_real_endpoint hN htlo)
  have hqpos : (0 : Real) < q := by exact_mod_cast (by omega : 0 < q)
  have hqone : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqlog : Real.log q ≤ 6 * Real.log (sourceL N) := by
    have h := Real.log_le_log hqpos hqUpper
    change Real.log q ≤ Real.log (sourceL N ^ (6 : Nat)) at h
    simpa [Real.log_pow] using h
  have hsmall := nat_mul_log_lt (k := 6) hL (by norm_num)
  norm_num only [Nat.cast_ofNat] at hsmall
  have hlog : Real.log q / 2 + 15 / 2 ≤ sourceL N := by linarith
  have hlog0 : 0 ≤ Real.log q / 2 + 15 / 2 := by
    linarith [Real.log_nonneg hqone]
  have hheight : (sourceT N + 1) ^ 2 + 4 ≤ 8 * sourceT N ^ 2 := by
    nlinarith [sq_nonneg (sourceT N - 1)]
  have hcoarse : 2 * Real.sqrt t * ((sourceT N + 1) ^ 2 + 4) *
      (Real.log q / 2 + 15 / 2) ≤ 16 * Real.sqrt t * sourceT N ^ 2 * sourceL N := by
    calc
      _ ≤ 2 * Real.sqrt t * (8 * sourceT N ^ 2) * sourceL N :=
        mul_le_mul (mul_le_mul_of_nonneg_left hheight (by positivity)) hlog hlog0 (by positivity)
      _ = _ := by ring
  have hsqrt := source_sqrt_endpoint_ge_large_power hN htlo
  have hpay : 16 * sourceT N ^ (3 : Nat) ≤ Real.sqrt t / 100000 * sourceL N := by
    have h := mul_le_mul_of_nonneg_right hsqrt hL0.le
    have heq : sourceL N ^ (44 : Nat) * sourceL N = sourceT N ^ (3 : Nat) := by
      unfold sourceT
      ring
    have hh : 2000000 * sourceT N ^ (3 : Nat) ≤ Real.sqrt t * sourceL N := by
      calc
        _ = (2000000 * sourceL N ^ (44 : Nat)) * sourceL N := by rw [mul_assoc, heq]
        _ ≤ _ := h
    nlinarith [pow_nonneg hT0.le 3]
  apply hcoarse.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hT0).mpr
  calc
    _ = (16 * sourceT N ^ (3 : Nat)) * (Real.sqrt t * sourceL N) := by ring
    _ ≤ (Real.sqrt t / 100000 * sourceL N) * (Real.sqrt t * sourceL N) :=
      mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = (1 / 100000 : Real) * (Real.sqrt t) ^ 2 * sourceL N ^ (2 : Nat) := by ring
    _ = _ := by rw [Real.sq_sqrt ht0.le]

theorem norm_lowZero_centered_sum_source_le
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) (hqUpper : (q : Real) ≤ sourceP1 N)
    {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    ‖∑ p ∈ lowZeroFinset hchi hPrimitive (sourceT N + 1),
      (((t : Complex) ^ completedZeroValue p -
        (2.5 : Complex) ^ completedZeroValue p) / completedZeroValue p)‖ ≤
      (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat) := by
  obtain ⟨_, ht, _⟩ := HorizontalEstimate.source_horizontal_parameters hN htlo hthi
  exact (norm_lowZero_centered_sum_le hchi hPrimitive (by linarith : 2.5 ≤ t)
    (sourceT N + 1)).trans (lowZero_explicit_cost_le_small_budget hN hq hqUpper htlo)

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical
