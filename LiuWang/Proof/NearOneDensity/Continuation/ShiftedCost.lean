import LiuWang.Proof.NearOneDensity.Continuation.PrincipalEuler

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Complex Finset Filter
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity.Continuation

theorem sum_shift_three_halves {a : ℝ} (ha : 3 / 2 ≤ a) (n : ℕ) :
    (∑ j ∈ range n, 1 / ((j : ℝ) + a) ^ 2) ≤ 1 := by
  have hh : (∑ j ∈ range n, 1 / ((j : ℝ) + a) ^ 2) ≤
      ∑ j ∈ range n, (1 / ((j : ℝ) + 1) - 1 / ((↑(j + 1) : ℝ) + 1)) := by
    apply sum_le_sum
    intro j _
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have he : 1 / ((j : ℝ) + 1) - 1 / ((↑(j + 1) : ℝ) + 1) =
        1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by push_cast; field_simp; ring
    rw [he]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_nonneg (a - 3 / 2)]
  rw [sum_range_sub'] at hh
  norm_num only [Nat.cast_zero, zero_add, div_one] at hh
  linarith [show 0 ≤ 1 / ((n : ℝ) + 1) by positivity]

theorem shifted_digamma_down {a b : ℝ} (ha : 3 / 2 ≤ a) (hab : a ≤ b) (y : ℝ) :
    (Complex.digamma ((a : ℂ) + I * y)).re - (Complex.digamma ((b : ℂ) + I * y)).re ≤
      (b - a) / 4 := by
  have ha0 : 0 < a := by linarith
  have hs := digamma_difference_hasSum ha0 (ha0.trans_le hab) y
  apply le_of_tendsto hs.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro n
  calc
    _ ≤ ∑ j ∈ range n, (b - a) / 4 * (1 / ((j : ℝ) + a) ^ 2) := by
      apply sum_le_sum
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have hh := reciprocal_difference_le (a := (j : ℝ) + a) (b := (j : ℝ) + b)
        (by linarith) (by linarith) y
      convert! hh using 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (b - a) / 4 * ∑ j ∈ range n, 1 / ((j : ℝ) + a) ^ 2 := by rw [mul_sum]
    _ ≤ (b - a) / 4 * 1 := mul_le_mul_of_nonneg_left (sum_shift_three_halves ha n) (by positivity)
    _ = _ := mul_one _

theorem shiftedGamma_row_function {σ : ℝ} (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) (t : ℝ) :
    shiftedGammaDifference σ t ≤
      stechkinConductorCoeff * (Real.log (max 1 |t|) - Real.log Real.pi) +
        (203 / 400) * (1 - stechkinK) + stechkinK / 24 := by
  have hge := stechkinSigma_ge hσ
  have hgap := stechkinSigma_sub_le hσ
  have hu := digamma_shift_up_le (a := 1) (b := σ / 2 + 1) le_rfl (by linarith) (t / 2)
  have hl := shifted_digamma_down (a := σ / 2 + 1) (b := stechkinSigma σ / 2 + 1)
    (by linarith) (by linarith) (t / 2)
  have href := digamma_one_re_le_log_max (t / 2)
  norm_num only [Complex.ofReal_one] at hu
  have hlog : 2 * |t / 2| = |t| := by rw [abs_div]; norm_num; ring
  rw [hlog] at href
  have ha : (Complex.digamma (((σ / 2 + 1 : ℝ) : ℂ) + I * (t / 2 : ℝ))).re ≤
      Real.log (max 1 |t|) + 203 / 200 := by linarith
  have h1 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr stechkinK_mem.2)
  have h2 := mul_le_mul_of_nonneg_left hl stechkinK_mem.1
  have h3 := mul_le_mul_of_nonneg_left hgap stechkinK_mem.1
  have hcast (u : ℝ) : ((u : ℂ) + I * t) / 2 + 1 =
      (((u / 2 + 1 : ℝ) : ℂ) + I * (t / 2 : ℝ)) := by push_cast; ring
  unfold shiftedGammaDifference
  rw [hcast, hcast]
  dsimp [stechkinConductorCoeff]
  nlinarith

theorem log_pi_ge_114 : (114 / 100 : ℝ) ≤ Real.log Real.pi := by
  have hp := Real.log_le_log (by norm_num : (0 : ℝ) < 314 / 100)
    (show (314 / 100 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_d2])
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / (314 / 100))
  rw [Real.log_div (by norm_num) (by norm_num)] at hh
  norm_num at hh
  linarith [Real.log_three_gt_d9]

theorem principal_high_constant :
    stechkinConductorCoeff * (Real.log 2 - Real.log Real.pi) +
      (203 / 400) * (1 - stechkinK) + stechkinK / 24 + 941 / 1600 ≤ 0.7647 := by
  have hk := stechkinK_mem
  have hlog : Real.log 2 - Real.log Real.pi ≤ 694 / 1000 - 114 / 100 := by
    linarith [Real.log_two_lt_d9, log_pi_ge_114]
  have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ stechkinConductorCoeff by
    unfold stechkinConductorCoeff
    linarith [hk.2])
  dsimp [stechkinConductorCoeff] at *
  linarith [stechkinK_ge_447]

end LiuWang.Proof.NearOneDensity.Continuation
