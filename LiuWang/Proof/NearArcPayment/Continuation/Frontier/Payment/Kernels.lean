import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Density

/-! 近一族不丢失实部权；整段高度用平方根核，同号较低高度用原非驻相核。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment

open Interfaces Parameters CompleteExpansion

theorem window_weight_le_two {beta : ℝ} (hb : 0.9 ≤ beta) :
    (0.001 : ℝ) ^ (beta - 1) ≤ 2 := by
  have hh : (0.001 : ℝ) ^ ((-1 : ℝ) / 10) ≤ 2 := by
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (by norm_num) _) (by norm_num)
      (by norm_num : (0 : ℝ) < 10)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 0.001)]
    norm_num
  exact (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
    (show (-1 : ℝ) / 10 ≤ beta - 1 by linarith)).trans hh

theorem Jrho_density_sqrt {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {rho : ℂ} (ha : densityAlpha N ≤ rho.re) (hb : rho.re ≤ 1)
    (hg : rho.im ≠ 0) (eta : ℝ) :
    ‖Jrho N rho eta‖ ≤ 20 * (N : ℝ) / Real.sqrt |rho.im| := by
  have hn := natCast_pos_of_exp_le hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have hp : (N : ℝ) ^ rho.re ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hb
  apply (OscillatoryBounds.Jrho_sqrt_ten (nat_pos_of_exp_le hN) hb hg eta).trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc
    _ ≤ 10 * 2 * (N : ℝ) := by
      apply mul_le_mul _ hp (Real.rpow_nonneg hn.le _) (by norm_num)
      exact mul_le_mul_of_nonneg_left
        (window_weight_le_two ((densityAlpha_ge_nine_tenths hN).trans ha)) (by norm_num)
    _ = _ := by ring

theorem Jrho_density_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ} {positive : Bool}
    (hr : rho ∈ densityValues chi N positive) {eta : ℝ}
    (he : if positive then 0 ≤ eta else eta ≤ 0) :
    ‖Jrho N rho eta‖ ≤ 20 * (N : ℝ) / sourceL N ^ 3 := by
  have hL := sourceL_pos hN
  have hn := natCast_pos_of_exp_le hN
  obtain ⟨hr, ha, hh⟩ := Finset.mem_filter.mp hr
  have hf := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  obtain ⟨_, h0, h1, _⟩ := (finalValues_literal chi).mp hf
  rcases hh with hh | ⟨hh, hs⟩
  · have hg : rho.im ≠ 0 := abs_pos.mp ((pow_pos hL 6).trans_le hh)
    have hsqrt : sourceL N ^ 3 ≤ Real.sqrt |rho.im| := by
      apply (Real.le_sqrt (pow_nonneg hL.le 3) (abs_nonneg _)).mpr
      simpa only [← pow_mul] using hh
    exact (Jrho_density_sqrt hN ha h1.le hg eta).trans
      (div_le_div_of_nonneg_left (by positivity) (pow_pos hL 3) hsqrt)
  · have hg : rho.im ≠ 0 := abs_pos.mp ((pow_pos hL 4).trans_le hh)
    have hsign : 0 ≤ eta * rho.im := by
      cases positive
      · exact mul_nonneg_of_nonpos_of_nonpos he (le_of_lt hs)
      · exact mul_nonneg he (le_of_lt hs)
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
    have hp : (N : ℝ) ^ rho.re ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 h1.le
    calc
      _ ≤ 4000 * (N : ℝ) ^ rho.re / |rho.im| :=
        Jrho_sameSign (nat_pos_of_exp_le hN) h0.le h1.le hg hsign
      _ ≤ 4000 * (N : ℝ) / sourceL N ^ 4 :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hp (by norm_num))
          (pow_pos hL 4) hh
      _ = (4000 * (N : ℝ) / sourceL N) / sourceL N ^ 3 := by
        rw [show sourceL N ^ 4 = sourceL N * sourceL N ^ 3 by ring, div_mul_eq_div_div]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hL.le 3)
        apply (div_le_iff₀ hL).mpr
        have hl : (4000 : ℝ) ≤ 20 * sourceL N := by linarith [sourceL_ge_2000 hN]
        nlinarith [mul_le_mul_of_nonneg_right hl hn.le]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment
