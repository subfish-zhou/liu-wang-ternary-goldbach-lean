import LiuWang.Proof.SourceRoute.Density.Restart.FamilyProduct

/-! A paid positive right edge for Chen's whole product, with the original center constant. -/

set_option autoImplicit false

noncomputable section

open Complex Finset
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.SourceRoute.Density.Restart

theorem familySquare_two_le (q : ℕ) [NeZero q] {X : ℝ} (hX : 1 < X)
    {s : ℂ} (hs : s.re = 2) :
    familySquare q X s ≤ (q.totient - 1 : ℕ) * (4 / (X - 1) ^ 2) := by
  have h := sum_le_sum (s := nonprincipalCharacters q) (fun chi _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_f_two_le chi hs hX) 2)
  rw [sum_const, nsmul_eq_mul, card_nonprincipalCharacters] at h
  simpa only [familySquare, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

theorem familySquare_two_small (q : ℕ) [NeZero q] {X : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) {s : ℂ} (hs : s.re = 2) :
    familySquare q X s ≤ 1 / 10000 := by
  have hphi : ((q.totient - 1 : ℕ) : ℝ) ≤ X :=
    (Nat.cast_le.mpr ((Nat.sub_le _ _).trans (Nat.totient_le q))).trans hqX
  apply (familySquare_two_le q (by linarith) hs).trans
  apply le_trans (mul_le_mul_of_nonneg_right hphi (by positivity))
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < X - 1))).mpr
  nlinarith [mul_nonneg (show 0 ≤ X - 100000 by linarith) (show 0 ≤ X by linarith)]

theorem familyProduct_right_distance (q : ℕ) [NeZero q] {X : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) {s : ℂ} (hs : s.re = 2) :
    ‖familyProduct q X s - 1‖ ≤ 1 / 9999 := by
  have he := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    (by norm_num : (1 / 10000 : ℝ) < 1)
  have h := (norm_familyProduct_sub_one_le q X s).trans
    (sub_le_sub_right ((Real.exp_le_exp.mpr (familySquare_two_small q hX hqX hs)).trans he) 1)
  norm_num at h
  exact h

theorem familyProduct_right_re (q : ℕ) [NeZero q] {X : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) {s : ℂ} (hs : s.re = 2) :
    1 - 1 / 9999 ≤ (familyProduct q X s).re := by
  have hr := (Complex.abs_re_le_norm (familyProduct q X s - 1)).trans
    (familyProduct_right_distance q hX hqX hs)
  simp only [sub_re, one_re] at hr
  linarith [(abs_le.mp hr).1]

theorem source_height_ge_one {q : ℕ} (hq : 3 ≤ q) {T : ℝ}
    (hT : 10000 * Real.log q ≤ T) : 1 ≤ T := by
  have hqR : (3 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hlog := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < q)
  have hinv : (q : ℝ)⁻¹ ≤ 1 / 3 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hqR
  linarith

theorem source_q_le_cutoff {q : ℕ} (hq : 3 ≤ q) {T : ℝ}
    (hT : 10000 * Real.log q ≤ T) : (q : ℝ) ≤ (q : ℝ) * T := by
  have h := mul_le_mul_of_nonneg_left (source_height_ge_one hq hT) (Nat.cast_nonneg q)
  simpa only [mul_one] using h

end LiuWang.Proof.SourceRoute.Density.Restart
