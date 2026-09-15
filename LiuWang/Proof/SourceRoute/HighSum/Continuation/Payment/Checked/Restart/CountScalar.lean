import LiuWang.Proof.DirichletZeroCount.Remainder.SourceFamily
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The literal decimal count bound in (2.25), from stronger frozen counts -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

def source25Bound (q : ℕ) (y : ℝ) : ℝ :=
  y / Real.pi * Real.log ((q : ℝ) * y) - 0.874 * y +
    6.8423 * Real.log ((q : ℝ) * y) + 15

theorem log_two_pi_lower : (7 / 4 : ℝ) ≤ Real.log (2 * Real.pi) := by
  have h := Real.sum_range_le_log_div (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 1
  norm_num at h
  have h6 : Real.log 6 = 2 * Real.log 2 + Real.log (3 / 2) := by
    have hh := Real.log_mul (by norm_num : (2 : ℝ) ^ (2 : ℕ) ≠ 0)
      (by norm_num : (3 / 2 : ℝ) ≠ 0)
    rw [Real.log_pow] at hh
    norm_num at hh
    exact hh
  have hp := Real.log_le_log (by norm_num : (0 : ℝ) < 6)
    (by linarith [Real.pi_gt_three] : (6 : ℝ) ≤ 2 * Real.pi)
  rw [h6] at hp
  linarith [Real.log_two_gt_d9]

theorem gamma_phase_upper {a y : ℝ} (ha : 1 ≤ a) (hy : 0 < y) :
    sourceGammaMain a y ≤ y * Real.log (y / 2) - y + a + (a - 1) * (Real.pi / 2) := by
  let r := ‖(a : ℂ) + (y : ℂ) * Complex.I‖
  have hr : 0 < r := lt_of_lt_of_le hy (by simpa [r] using im_le_norm ((a : ℂ) + (y : ℂ) * Complex.I))
  have hn : r ≤ y + a := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by simp [abs_of_pos hy, abs_of_nonneg (by linarith : 0 ≤ a)]; ring
  have hl := Real.log_le_sub_one_of_pos (div_pos hr hy)
  have hd : Real.log (r / 2) - Real.log (y / 2) = Real.log (r / y) := by
    rw [Real.log_div hr.ne' (by norm_num), Real.log_div hy.ne' (by norm_num),
      Real.log_div hr.ne' hy.ne']
    ring
  have hh : y * (Real.log (r / 2) - Real.log (y / 2)) ≤ a := by
    rw [hd]
    have ht := mul_le_mul_of_nonneg_left hl hy.le
    field_simp at ht
    nlinarith
  have hat := mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two (y / a)).le
    (sub_nonneg.mpr ha)
  unfold sourceGammaMain
  change y * Real.log (r / 2) - y + (a - 1) * Real.arctan (y / a) ≤ _
  nlinarith

theorem shifted_log_upper {y : ℝ} (hy : 3.36 ≤ y) :
    Real.log (y + 2) ≤ Real.log y + 3 / 5 := by
  have hy0 : 0 < y := by linarith
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (y + 2) / y)
  rw [Real.log_div (by positivity) hy0.ne'] at h
  have hd : (y + 2) / y - 1 ≤ (3 / 5 : ℝ) := by
    have hh : (y + 2) / y ≤ 3 / 5 + 1 := (div_le_iff₀ hy0).mpr (by linarith)
    linarith
  linarith

theorem count_scalar_payment {y s : ℝ} (hy : 0 ≤ y) (hs : 10 ≤ s) :
    (y * s - (7 / 4 + 1) * y + (5 * Real.pi / 2 + 4) * s +
      35 * Real.pi) / Real.pi ≤
      y / Real.pi * s - 0.874 * y + 6.8423 * s + 15 := by
  have hp0 := Real.pi_pos
  have hp := Real.pi_gt_d2
  have hp' := Real.pi_lt_d4
  apply (div_le_iff₀ hp0).mpr
  field_simp
  have h1 := mul_nonneg hy (by linarith : 0 ≤ 7 / 4 + 1 - 0.874 * Real.pi)
  have h2 := mul_nonneg (sub_nonneg.mpr hs)
    (by linarith : 0 ≤ 6.8423 * Real.pi - (5 * Real.pi / 2 + 4))
  nlinarith

theorem nonprincipal_uniform_le_source25 {q : ℕ} [NeZero q] (chi : Character q)
    {y : ℝ} (hy : 3.36 ≤ y) (hs : 10 ≤ Real.log ((q : ℝ) * y)) :
    uniformCountBound q (parityShift chi) y ≤ source25Bound q y := by
  have hy0 : 0 < y := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hg := (parity_gamma_le_odd chi hy0.le).trans (gamma_phase_upper (by norm_num) hy0)
  have hlog := shifted_log_upper hy
  have he : Real.log ((q : ℝ) / Real.pi) + Real.log (y / 2) =
      Real.log ((q : ℝ) * y) - Real.log (2 * Real.pi) := by
    rw [Real.log_div hq0.ne' Real.pi_ne_zero, Real.log_div hy0.ne' (by norm_num),
      Real.log_mul hq0.ne' hy0.ne', Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  have hcoeff : 0 ≤ 5 * Real.pi / 2 + 4 := by positivity
  have hh := mul_le_mul_of_nonneg_left hlog hcoeff
  have hL := mul_le_mul_of_nonneg_left log_two_pi_lower hy0.le
  apply le_trans _ (count_scalar_payment hy0.le hs)
  unfold uniformCountBound uniformHorizontalFee
  rw [abs_of_pos hy0]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have hs' : Real.log q + Real.log y = Real.log ((q : ℝ) * y) :=
    (Real.log_mul hq0.ne' hy0.ne').symm
  have he' := congrArg (fun x : ℝ => y * x) he
  nlinarith [Real.pi_gt_three]

theorem principal_uniform_le_source25 {q : ℕ} [NeZero q] {y : ℝ}
    (hy : 3.36 ≤ y) (hs : 10 ≤ Real.log ((q : ℝ) * y)) :
    uniformXiCountBound y ≤ source25Bound q y := by
  have hy0 : 0 < y := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (NeZero.pos q))
  have hg := gamma_phase_upper (a := 4) (by norm_num) hy0
  have hlog := shifted_log_upper hy
  have he : Real.log (y / 2) - Real.log Real.pi =
      Real.log y - Real.log (2 * Real.pi) := by
    rw [Real.log_div hy0.ne' (by norm_num), Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  have hcoeff : 0 ≤ 5 * Real.pi / 2 + 4 := by positivity
  have hh := mul_le_mul_of_nonneg_left hlog hcoeff
  have hL := mul_le_mul_of_nonneg_left log_two_pi_lower hy0.le
  have hq1 := mul_nonneg hy0.le hqlog
  have hq2 := mul_nonneg hcoeff hqlog
  apply le_trans _ (count_scalar_payment hy0.le hs)
  unfold uniformXiCountBound uniformXiFee
  rw [abs_of_pos hy0]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have hs' : Real.log q + Real.log y = Real.log ((q : ℝ) * y) :=
    (Real.log_mul hq0.ne' hy0.ne').symm
  have he' := congrArg (fun x : ℝ => y * x) he
  nlinarith [Real.pi_gt_three]

theorem count_le_source25 {q : ℕ} [NeZero q] (chi : Character q) {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 3.36 ≤ y) (hs : 10 ≤ Real.log ((q : ℝ) * y)) :
    (count chi alpha y : ℝ) ≤ source25Bound q y := by
  by_cases hc : chi = 1
  · subst chi
    exact (principal_count_alpha_le_uniform q ha (by linarith)).trans
      (principal_uniform_le_source25 hy hs)
  · exact (count_nonprincipal_uniform_modulus hc ha (by linarith)).trans
      (nonprincipal_uniform_le_source25 chi hy hs)

theorem familyCount_le_source25 {q : ℕ} [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 3.36 ≤ y) (hs : 10 ≤ Real.log ((q : ℝ) * y)) :
    (familyCount q alpha y : ℝ) ≤ (q.totient : ℝ) * source25Bound q y := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold familyCount
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _chi : Character q, source25Bound q y :=
      Finset.sum_le_sum (fun chi _ => count_le_source25 chi ha hy hs)
    _ = _ := by simp [hc]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
