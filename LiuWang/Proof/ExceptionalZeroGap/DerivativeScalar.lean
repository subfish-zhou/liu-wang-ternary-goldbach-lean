import LiuWang.Proof.ExceptionalZeroGap.DerivativeHead

/-!
# 原常数的有理数证书

`c1 = 9.645908801`，`y = 13 sqrt r`。所有数值吸收由实数不等式、
已证对数界及有限 Taylor 界支付，不使用浮点判定。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ExceptionalZeroGap

open Finset

def c1 : ℝ := 9.645908801

def nearOneLower (x : ℝ) : ℝ := 1 - 1 / (c1 * Real.log x)

theorem log_thirteen_le : Real.log 13 ≤ 2.565 := by
  have h := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 1 / 25) (by norm_num : (1 / 25 : ℝ) < 1) 2
  norm_num [sum_range_succ] at h
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  have h12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [h12] at h
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem log_large_conductor_lower {r : ℕ} (hr : 987 ≤ r) :
    6.894 ≤ Real.log (r : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 972 / 987)
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  have h972 : Real.log 972 = 2 * Real.log 2 + 5 * Real.log 3 := by
    rw [show (972 : ℝ) = 2 ^ 2 * 3 ^ 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [h972] at h
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 987)
    (show (987 : ℝ) ≤ r by exact_mod_cast hr)
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem log_chosen_cutoff_le {r : ℕ} (hr : 987 ≤ r) :
    Real.log (13 * Real.sqrt r) ≤ 0.8721 * Real.log r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  rw [Real.log_mul (by norm_num) (Real.sqrt_pos.2 hr0).ne', Real.log_sqrt hr0.le]
  linarith [log_thirteen_le, log_large_conductor_lower hr]

theorem chosen_cutoff_ge_ten {r : ℕ} (hr : 987 ≤ r) :
    10 ≤ 13 * Real.sqrt r := by
  have hs : (1 : ℝ) ≤ Real.sqrt r := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast (show 1 ≤ r by omega)
  linarith

theorem finite_head_constant_le :
    -(1 / 2 : ℝ) * (Real.log 3) ^ 2 + Real.log 3 / 3 + Real.log 2 / 2 ≤ 0.1094 := by
  have hsq : (1.0986122885 : ℝ) ^ 2 ≤ (Real.log 3) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith [Real.log_three_gt_d9])).2
      Real.log_three_gt_d9.le
  nlinarith [Real.log_three_lt_d9, Real.log_two_lt_d9]

theorem chosen_head_tail_coefficient_le {r : ℕ} (hr : 987 ≤ r) :
    finiteHeadBudget (13 * Real.sqrt r) +
        Real.sqrt r * Real.log r * Real.log (13 * Real.sqrt r) / (13 * Real.sqrt r) ≤
      0.4497 * (Real.log r) ^ 2 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.2 hr0).ne'
  have htail :
      Real.sqrt r * Real.log r * Real.log (13 * Real.sqrt r) / (13 * Real.sqrt r) =
        Real.log r * Real.log (13 * Real.sqrt r) / 13 := by
    field_simp
  rw [htail]
  have hL := log_large_conductor_lower hr
  have hy := log_chosen_cutoff_le hr
  have hy0 : 0 ≤ Real.log (13 * Real.sqrt r) :=
    Real.log_nonneg (by linarith [chosen_cutoff_ge_ten hr])
  have hsq := (sq_le_sq₀ hy0 (by positivity : 0 ≤ 0.8721 * Real.log (r : ℝ))).2 hy
  have hmul := mul_le_mul_of_nonneg_left hy (by linarith : 0 ≤ Real.log (r : ℝ))
  have hLsq : (6.894 : ℝ) ^ 2 ≤ (Real.log (r : ℝ)) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith)).2 hL
  unfold finiteHeadBudget
  nlinarith [finite_head_constant_le]

theorem half_le_nearOneLower {x : ℝ} (hx : 10 ≤ x) :
    1 / 2 ≤ nearOneLower x := by
  have hlog := two_le_log_of_ten_le hx
  have hd : 0 < c1 * Real.log x := by unfold c1; positivity
  have hdiv : 1 / (c1 * Real.log x) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hd).2
    unfold c1
    linarith
  unfold nearOneLower
  linarith

theorem exp_cutoff_ratio_le : Real.exp (0.8721 / c1) ≤ 1.0947 := by
  have harg : (0.8721 : ℝ) / c1 ≤ 0.09042 := by norm_num [c1]
  refine (Real.exp_le_exp.mpr harg).trans ?_
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.09042)
    (by norm_num : (0.09042 : ℝ) ≤ 1) (by norm_num : 0 < (5 : ℕ))
  refine h.trans ?_
  norm_num [sum_range_succ, Nat.factorial]

theorem chosen_power_le {r : ℕ} (hr : 987 ≤ r) {x σ : ℝ}
    (hx : 10 ≤ x) (hrx : (r : ℝ) ≤ x) (hσ : nearOneLower x ≤ σ) :
    (13 * Real.sqrt r) ^ (1 - σ) ≤ 1.0947 := by
  have hL := log_large_conductor_lower hr
  have hX := two_le_log_of_ten_le hx
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hy0 : 0 < 13 * Real.sqrt (r : ℝ) := by positivity
  have hylog : 0 ≤ Real.log (13 * Real.sqrt r) :=
    Real.log_nonneg (by linarith [chosen_cutoff_ge_ten hr])
  have hd : 0 < c1 * Real.log x := by unfold c1; positivity
  have hlog : Real.log (13 * Real.sqrt r) ≤ 0.8721 * Real.log x :=
    (log_chosen_cutoff_le hr).trans
      (mul_le_mul_of_nonneg_left (Real.log_le_log hr0 hrx) (by norm_num))
  have hexp : Real.log (13 * Real.sqrt r) * (1 - σ) ≤ 0.8721 / c1 := by
    calc
      _ ≤ Real.log (13 * Real.sqrt r) * (1 / (c1 * Real.log x)) :=
        mul_le_mul_of_nonneg_left (by unfold nearOneLower at hσ; linarith) hylog
      _ = Real.log (13 * Real.sqrt r) / (c1 * Real.log x) := by ring
      _ ≤ 0.8721 / c1 := by
        apply (div_le_iff₀ hd).2
        calc
          _ ≤ 0.8721 * Real.log x := hlog
          _ = _ := by unfold c1; ring
  rw [Real.rpow_def_of_pos hy0]
  exact (Real.exp_le_exp.mpr hexp).trans exp_cutoff_ratio_le

end LiuWang.Proof.ExceptionalZeroGap
