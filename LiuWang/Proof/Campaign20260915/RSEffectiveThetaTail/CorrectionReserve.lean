import LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.SpectralSplit

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

theorem trivialKernel_le_inv_sq {x : ℝ} (hx : 2 ≤ x) :
    rsTrivialKernel x ≤ x⁻¹ ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hi2 : x⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hx
  have hy : x⁻¹ ^ 2 ≤ 1 / 4 := by nlinarith
  have hd : 0 < 1 - x⁻¹ ^ 2 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [Real.log_inv] at hlog
  have hfrac : (1 - x⁻¹ ^ 2)⁻¹ - 1 ≤ 2 * x⁻¹ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hd).mp
    have hid : (1 - x⁻¹ ^ 2) * ((1 - x⁻¹ ^ 2)⁻¹ - 1) = x⁻¹ ^ 2 := by
      rw [mul_sub, mul_inv_cancel₀ hd.ne', mul_one]
      ring
    rw [hid]
    nlinarith [sq_nonneg (x⁻¹ ^ 2)]
  unfold rsTrivialKernel
  linarith

theorem half_log_ge_saddle {L : ℝ} (hL : 5000 ≤ L) :
    saddle L ≤ L / 2 := by
  have hs := saddle_ge_sixteen hL
  have hsid : L = rsR * saddle L ^ 2 := by
    rw [saddle_sq (by linarith : 0 ≤ L)]
    field_simp [rsR_pos.ne']
  have h := mul_le_mul_of_nonneg_right
    (show (16 : ℝ) ≤ rsR by linarith [rsR_interval.1]) (sq_nonneg (saddle L))
  nlinarith

theorem exponential_correction_reserve {L : ℝ} (hL : 5000 ≤ L) :
    (1.84 : ℝ) * Real.exp (-L) + Real.log 4 * Real.exp (-L / 2) +
      3 * Real.exp (-2 * L / 3) +
      rsTrivialKernel (Real.exp L) / Real.exp L ≤ epsilon (Real.exp L) / 8 := by
  have hs := saddle_ge_sixteen hL
  have heL : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hi : (Real.exp L)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) heL
  have hi0 : 0 ≤ (Real.exp L)⁻¹ := (inv_pos.mpr (Real.exp_pos L)).le
  have hk : rsTrivialKernel (Real.exp L) ≤ 1 := by
    have h := trivialKernel_le_inv_sq heL
    nlinarith
  have hK : rsTrivialKernel (Real.exp L) / Real.exp L ≤ Real.exp (-L / 2) := by
    calc
      _ ≤ 1 / Real.exp L := div_le_div_of_nonneg_right hk (Real.exp_pos _).le
      _ = Real.exp (-L) := by rw [Real.exp_neg, one_div]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have he1 : (1.84 : ℝ) * Real.exp (-L) ≤ 2 * Real.exp (-L / 2) :=
    mul_le_mul (by norm_num) (Real.exp_le_exp.mpr (by linarith))
      (Real.exp_pos _).le (by norm_num)
  have he2 := mul_le_mul_of_nonneg_right hlog4 (Real.exp_pos (-L / 2)).le
  have he3 := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (show -2 * L / 3 ≤ -L / 2 by linarith))
    (show (0 : ℝ) ≤ 3 by norm_num)
  have he4 : 8 * Real.exp (-L / 2) ≤ 8 * Real.exp (-saddle L) :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith [half_log_ge_saddle hL])) (by norm_num)
  have he5 := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-saddle L)).le
  have heps := original_epsilon_lower (x := Real.exp L) (by simpa using hL)
  rw [Real.log_exp] at heps
  linarith

theorem elementary_correction_reserve {x : ℝ} (hx : 0 < x)
    (hL : 5000 ≤ Real.log x) :
    1.84 + Real.log 4 * Real.sqrt x + 3 * x ^ (1 / (3 : ℝ)) +
      rsTrivialKernel x ≤ x * epsilon x / 8 := by
  let L := Real.log x
  have hex : Real.exp L = x := Real.exp_log hx
  have he0 : Real.exp L * Real.exp (-L) = 1 := by
    rw [← Real.exp_add]
    simp
  have hehalf : Real.exp L * Real.exp (-L / 2) = Real.sqrt x := by
    rw [← Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    dsimp [L]
    ring
  have hethird : Real.exp L * Real.exp (-2 * L / 3) = x ^ (1 / (3 : ℝ)) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos hx]
    congr 1
    dsimp [L]
    ring
  have h := mul_le_mul_of_nonneg_left (exponential_correction_reserve hL) (Real.exp_pos L).le
  have hK : Real.exp L * (rsTrivialKernel x / Real.exp L) = rsTrivialKernel x := by
    field_simp
  rw [hex] at he0 hehalf hethird hK h
  have hehalf' := congrArg (fun t : ℝ => Real.log 4 * t) hehalf
  dsimp [L] at he0 hethird hehalf'
  nlinarith

#print axioms trivialKernel_le_inv_sq
#print axioms elementary_correction_reserve

end LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail
