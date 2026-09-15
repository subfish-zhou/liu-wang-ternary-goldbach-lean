import LiuWang.Proof.ExplicitPerron.Main
import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.LowBudget

/-!
# Scalar bounds for the original closed Perron error

The estimates retain the literal `2^b` coefficient. The large endpoint bound
is derived from the existing `L^96 ≤ N`, not an additional hypothesis.
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ExplicitPerron

namespace LiuWang.Proof.PerronBudget

theorem log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h

theorem log_four_add_four_le : Real.log 4 + 4 ≤ 6 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  linarith [log_two_bounds.2]

theorem source_series_factor {L : ℝ} (hL : 2000 ≤ L) :
    0 ≤ (Real.log 4 + 4) * (1 + 1 / L) / ((1 + 1 / L) - 1) ∧
    (Real.log 4 + 4) * (1 + 1 / L) / ((1 + 1 / L) - 1) ≤ 6.01 * L := by
  have hL0 : 0 < L := by linarith
  have heq : (Real.log 4 + 4) * (1 + 1 / L) / ((1 + 1 / L) - 1) =
      (Real.log 4 + 4) * (L + 1) := by field_simp; ring
  rw [heq]
  constructor
  · positivity
  · calc
      _ ≤ 6 * (L + 1) := mul_le_mul_of_nonneg_right log_four_add_four_le (by positivity)
      _ ≤ _ := by linarith

theorem source_two_rpow_le_three {L : ℝ} (hL : 2000 ≤ L) :
    (2 : ℝ) ^ (1 + 1 / L) ≤ 3 := by
  have hL0 : 0 < L := by linarith
  have hb : 1 + 1 / L ≤ (3 / 2 : ℝ) := by
    have hh : 1 / L ≤ (1 / 2 : ℝ) := (div_le_iff₀ hL0).mpr (by linarith)
    linarith
  have hp : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = 8 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hc : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (3 / 2 : ℝ)]
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hb).trans hc

theorem source_log_bounds {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {x : ℝ} (hx : 1 ≤ x) (hxN : x ≤ 2 * (N : ℝ)) :
    0 ≤ Real.log x ∧ Real.log x ≤ sourceL N + 1 ∧
    0 ≤ Real.log (2 * x) ∧ Real.log (2 * x) ≤ sourceL N + 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast nat_pos_of_exp_le hN
  have hx0 : 0 < x := by linarith
  have hh := Real.log_le_log hx0 hxN
  rw [Real.log_mul (by norm_num) hN0.ne'] at hh
  have hh2 : Real.log (2 * x) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) hx0.ne'
  dsimp [sourceL]
  refine ⟨Real.log_nonneg hx, ?_, Real.log_nonneg (by linarith), ?_⟩
  · linarith [log_two_bounds.2]
  · linarith [log_two_bounds.2]

theorem source_rpow_small {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {x : ℝ} (hx : 1 ≤ x) (hxN : x ≤ 2 * (N : ℝ)) :
    x ^ (1 / sourceL N) ≤ 9 := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hlog := (source_log_bounds hN hx hxN).2.1
  have he : Real.log x * (1 / sourceL N) ≤ 2 := by
    rw [mul_one_div]
    exact (div_le_iff₀ hL0).mpr (by linarith)
  calc
    _ = Real.exp (Real.log x * (1 / sourceL N)) := Real.rpow_def_of_pos (by linarith) _
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr he
    _ = (Real.exp 1) ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 3 ^ (2 : ℕ) := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _
    _ = 9 := by norm_num

theorem source_rpow_le_nine_mul {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {x : ℝ} (hx : 1 ≤ x) (hxN : x ≤ 2 * (N : ℝ)) :
    x ^ (1 + 1 / sourceL N) ≤ 9 * x := by
  rw [Real.rpow_add (by linarith : 0 < x), Real.rpow_one]
  nlinarith [mul_le_mul_of_nonneg_left (source_rpow_small hN hx hxN) (by linarith : 0 ≤ x)]

theorem million_sourceT_sq_le_endpoint {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {t : ℝ}
    (htlo : sourceWindowLower N ≤ t) :
    1000000 * sourceT N ^ (2 : ℕ) ≤ t := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hc : (1000000000 : ℝ) ≤ sourceL N ^ (3 : ℕ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2000) hL 3
    norm_num at hh
    linarith
  have hp : 1000000000 * sourceT N ^ (2 : ℕ) ≤ (N : ℝ) := by
    calc
      _ ≤ sourceL N ^ (3 : ℕ) * sourceT N ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = sourceL N ^ (33 : ℕ) := by unfold sourceT; ring
      _ ≤ sourceL N ^ (96 : ℕ) :=
        pow_le_pow_right₀ (one_le_sourceL hN) (by norm_num)
      _ ≤ Real.exp (sourceL N) :=
        LocalAnalyticBounds.LeftVertical.pow_ninety_six_le_exp hL
      _ = (N : ℝ) := exp_sourceL (nat_pos_of_exp_le hN)
  change (N : ℝ) / 1000 ≤ t at htlo
  linarith

theorem source_cutoff_bounds {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    1000000 ≤ t ∧ 1 ≤ halfCutoff t ∧ halfCutoff t ≤ 2 * (N : ℝ) ∧
    (5 / 2 : ℝ) ≤ 2 * (N : ℝ) ∧ halfCutoff t + 5 / 2 ≤ 1.001 * t ∧
    max (halfCutoff t) t ≤ 2 * (N : ℝ) := by
  have hT1 : 1 ≤ sourceT N := one_le_pow₀ (one_le_sourceL hN)
  have htbig : 1000000 ≤ t := by
    nlinarith [million_sourceT_sq_le_endpoint hN htlo, sq_nonneg (sourceT N - 1)]
  have ht0 : 0 ≤ t := by linarith
  have hh := (abs_le.mp (abs_sub_halfCutoff_le ht0))
  refine ⟨htbig, ?_, ?_, ?_, ?_, max_le ?_ ?_⟩ <;> linarith [hh.1, hh.2]

end LiuWang.Proof.PerronBudget
