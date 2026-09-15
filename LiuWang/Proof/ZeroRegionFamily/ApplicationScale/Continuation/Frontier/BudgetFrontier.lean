import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.LowHeight

/-! # 冻结四次无绝对费用母式的精确边界

下述严格不等式只说明删除全部剩余费用/核后，该固定系数母式在原R
不能靠调σ闭合。它不是关于真实L零点的反例，也不是原文的缺口。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

theorem conductor_coefficient_lower_tight : (276393/1000000 : ℝ) ≤ stechkinConductorCoeff := by
  have hp := Real.sqrt_pos.2 (show (0 : ℝ) < 5 by norm_num)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hlo : (2236067/1000000 : ℝ) ≤ Real.sqrt 5 := by nlinarith
  have hk : stechkinK ≤ 223607/500000 := by
    dsimp [stechkinK]
    apply (div_le_iff₀ hp).mpr
    linarith
  dsimp [stechkinConductorCoeff]
  linarith

theorem frozen_quartic_original_budget_strict {A : ℝ} (hA : 0 < A) :
    24480/(A+1/9.645908801) < 14379/A+46630*stechkinConductorCoeff := by
  let b : ℝ := 1/9.645908801
  let C : ℝ := 46630*(276393/1000000)
  have hC : 0 < C := by norm_num [C]
  have hb : 0 < b := by norm_num [b]
  have hdisc : (24480-14379-C*b)^2 < 4*C*14379*b := by norm_num [C, b]
  have hid : 4*C*(14379*(A+b)+C*A*(A+b)-24480*A) =
      (2*C*A-(24480-14379-C*b))^2+
        (4*C*14379*b-(24480-14379-C*b)^2) := by ring
  have hp : 0 < 4*C*(14379*(A+b)+C*A*(A+b)-24480*A) := by
    rw [hid]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sub_pos.mpr hdisc)
  have hn : 0 < 14379*(A+b)+C*A*(A+b)-24480*A :=
    (mul_pos_iff_of_pos_left (mul_pos (by norm_num) hC)).mp hp
  have he : ((14379/A+C)*(A+b)-24480)*A =
      14379*(A+b)+C*A*(A+b)-24480*A := by field_simp
  have hpaid : 24480/(A+b) < 14379/A+C := by
    apply (div_lt_iff₀ (add_pos hA hb)).mpr
    have hh : 0 < ((14379/A+C)*(A+b)-24480)*A := by rw [he]; exact hn
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hA).mp hh)
  have hk := mul_le_mul_of_nonneg_left conductor_coefficient_lower_tight
    (by norm_num : (0 : ℝ) ≤ 46630)
  exact hpaid.trans_le (add_le_add_right hk _)

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
