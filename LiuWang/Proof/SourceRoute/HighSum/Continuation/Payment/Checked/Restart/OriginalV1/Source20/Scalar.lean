import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.Elementary

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20

theorem log_linear_bound {L : ℝ} (hL : 3100 ≤ L) :
    Real.log L ≤ 9 * L / 3100 := by
  have hL0 : 0 < L := by linarith
  have hbase : Real.log 3100 ≤ 9 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at he
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2)
      (show 5 / 2 ≤ Real.exp 1 by linarith) 9
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < L / 3100)
  rw [Real.log_div hL0.ne' (by norm_num)] at hh
  linarith

theorem original_source20_scalar {L : ℝ} (hL : 3100 ≤ L) :
    51 * L ^ 3 * Real.log L ^ 2 * Real.exp (-L / 20) ≤ Real.exp (-90) / L ^ 4 := by
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlog := log_linear_bound hL
  have hsq : Real.log L ^ 2 ≤ 81 * L ^ 2 / 3100 ^ 2 := by
    nlinarith [sq_nonneg (Real.log L - 9 * L / 3100)]
  have hdec := Source26Certificate.power_exp_le (x := 3100) (y := L)
    (c := 1 / 20) 9 (by norm_num) hL (by norm_num)
  norm_num only [show -(1 / 20 : ℝ) * L = -L / 20 by ring,
    show -(1 / 20 : ℝ) * 3100 = -155 by norm_num] at hdec
  have hex : (51 * 3100 ^ 7 * 81 : ℝ) ≤ Real.exp 65 := by
    have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718 / 1000) he 65
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    exact le_trans (by norm_num) hp
  have hfinal : (51 * 3100 ^ 7 * 81 : ℝ) * Real.exp (-155) ≤ Real.exp (-90) := by
    apply (mul_le_mul_of_nonneg_right hex (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]
    norm_num
  apply (le_div_iff₀ (pow_pos hL0 4)).mpr
  have h1 := mul_le_mul_of_nonneg_left hsq
    (by positivity : 0 ≤ 51 * L ^ 7 * Real.exp (-L / 20))
  have h2 := mul_le_mul_of_nonneg_left hdec
    (by norm_num : (0 : ℝ) ≤ 51 * 81 / 3100 ^ 2)
  calc
    _ = (51 * L ^ 7 * Real.exp (-L / 20)) * Real.log L ^ 2 := by ring
    _ ≤ (51 * L ^ 7 * Real.exp (-L / 20)) * (81 * L ^ 2 / 3100 ^ 2) := h1
    _ = (51 * 81 / 3100 ^ 2) * (L ^ 9 * Real.exp (-L / 20)) := by ring
    _ ≤ (51 * 81 / 3100 ^ 2) * (3100 ^ 9 * Real.exp (-155)) := by
      convert! h2 using 1
      norm_num
    _ = (51 * 3100 ^ 7 * 81) * Real.exp (-155) := by ring
    _ ≤ _ := hfinal

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20
