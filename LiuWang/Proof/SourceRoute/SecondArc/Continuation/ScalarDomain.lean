import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ActualCount
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation

def sourceNu (x : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x) +
    2.50637 / Real.log (Real.log x)

def scaling (L : ℝ) : ℝ := Real.sqrt (L / 3100)

theorem scaling_bounds {L : ℝ} (hL : 3100 ≤ L) :
    1 ≤ scaling L ∧ L = 3100 * scaling L ^ 2 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ L / 3100)
  refine ⟨?_, ?_⟩
  · unfold scaling
    exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ L / 3100)).mpr (by linarith)
  · unfold scaling
    linarith

theorem log_3100_bounds : 7 ≤ Real.log (3100 : ℝ) ∧ Real.log (3100 : ℝ) ≤ 8.05 := by
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3100)).mpr
    calc
      Real.exp 7 = Real.exp 1 ^ (7 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3 ^ (7 : ℕ) := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
      _ ≤ 3100 := by norm_num
  · apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3100)).mpr
    calc
      (3100 : ℝ) ≤ (2.718 : ℝ) ^ (8 : ℕ) * (1 + 0.05) := by norm_num
      _ ≤ Real.exp 1 ^ (8 : ℕ) * Real.exp 0.05 :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num)
          (by linarith [Real.exp_one_gt_d9]) _)
          (by linarith [Real.add_one_le_exp (0.05 : ℝ)]) (by norm_num) (by positivity)
      _ = Real.exp 8.05 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem log_27_le : Real.log (27 : ℝ) ≤ 3.5 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 27)).mpr
  calc
    (27 : ℝ) ≤ (2.7 : ℝ) ^ (3 : ℕ) * (1 + 0.5 + 0.5 ^ (2 : ℕ) / 2) := by norm_num
    _ ≤ Real.exp 1 ^ (3 : ℕ) * Real.exp 0.5 :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.exp_one_gt_d9]) _)
        (by nlinarith [Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.5)])
        (by norm_num) (by positivity)
    _ = Real.exp 3.5 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem log_ten_pi_le_35 : Real.log (10 * Real.pi) ≤ 3.5 := by
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 10 * Real.pi)).mpr
  calc
    10 * Real.pi ≤ (2.7 : ℝ) ^ (3 : ℕ) * (1 + 0.5 + 0.5 ^ (2 : ℕ) / 2) := by
      nlinarith [Real.pi_lt_d2]
    _ ≤ Real.exp 1 ^ (3 : ℕ) * Real.exp 0.5 :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.exp_one_gt_d9]) _)
        (by nlinarith [Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.5)])
        (by norm_num) (by positivity)
    _ = Real.exp 3.5 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem log_source_in_scaling {L : ℝ} (hL : 3100 ≤ L) :
    Real.log L = Real.log (3100 : ℝ) + 2 * Real.log (scaling L) := by
  have hs := scaling_bounds hL
  have hr : 0 < scaling L := by linarith
  conv_lhs => rw [hs.2]
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  norm_num

theorem original_upper_le_scaling {L : ℝ} (hL : 3100 ≤ L) :
    Real.log (10 * Real.pi * L ^ (7 : ℕ)) ≤ 60 * scaling L := by
  have hs := scaling_bounds hL
  have hr : 0 < scaling L := by linarith
  have hlog := Real.log_le_sub_one_of_pos hr
  rw [Real.log_mul (by positivity : 10 * Real.pi ≠ 0) (by positivity), Real.log_pow,
    log_source_in_scaling hL]
  norm_num only [Nat.cast_ofNat]
  linarith [log_3100_bounds.2, log_ten_pi_le_35]

theorem original_H_ge_scaling {L : ℝ} (hL : 3100 ≤ L) :
    3093 * scaling L ^ 2 ≤ L + Real.log (0.001 : ℝ) := by
  have hs := scaling_bounds hL
  have hlog : -7 ≤ Real.log (0.001 : ℝ) := by
    have he : Real.log (1000 : ℝ) ≤ 7 := by
      apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1000)).mpr
      calc
        (1000 : ℝ) ≤ (2.7 : ℝ) ^ (7 : ℕ) := by norm_num
        _ ≤ Real.exp 1 ^ (7 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
        _ = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [show (0.001 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  nlinarith [sq_nonneg (scaling L - 1)]

theorem source_loglog_bounds {L : ℝ} (hL : 3100 ≤ L) :
    3 ≤ Real.log (Real.log (L ^ (3 : ℕ))) ∧
      Real.log (Real.log (L ^ (3 : ℕ))) ≤ 3.5 * scaling L ^ 2 := by
  have hs := scaling_bounds hL
  have hr : 0 < scaling L := by linarith
  have hlogL : 7 ≤ Real.log L :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  constructor
  · apply (Real.le_log_iff_exp_le (by positivity : 0 < 3 * Real.log L)).mpr
    calc
      Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.72 : ℝ) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
      _ ≤ 3 * Real.log L := by nlinarith
  · have hb : 3 * Real.log L ≤ 27 * scaling L := by
      rw [log_source_in_scaling hL]
      linarith [log_3100_bounds.2, Real.log_le_sub_one_of_pos hr]
    have hm := Real.log_le_log (by positivity : 0 < 3 * Real.log L) hb
    rw [Real.log_mul (by norm_num) hr.ne'] at hm
    nlinarith [log_27_le, Real.log_le_sub_one_of_pos hr, sq_nonneg (scaling L - 1)]

theorem sourceNu_le_scaling {L : ℝ} (hL : 3100 ≤ L) :
    0 ≤ sourceNu (L ^ (3 : ℕ)) ∧ sourceNu (L ^ (3 : ℕ)) ≤ 8 * scaling L ^ 2 := by
  have hs := scaling_bounds hL
  have hl := source_loglog_bounds hL
  have he : Real.exp Real.eulerMascheroniConstant ≤ 2 := by
    apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).mp
    linarith [Real.eulerMascheroniConstant_lt_two_thirds, Real.log_two_gt_d9]
  have hd : (2.50637 : ℝ) / Real.log (Real.log (L ^ (3 : ℕ))) ≤ 0.84 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  unfold sourceNu
  have hl0 : 0 ≤ Real.log (Real.log (L ^ (3 : ℕ))) := by linarith
  constructor
  · positivity
  · have hm := mul_le_mul he hl.2 (by linarith) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [sq_nonneg (scaling L - 1)]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation
