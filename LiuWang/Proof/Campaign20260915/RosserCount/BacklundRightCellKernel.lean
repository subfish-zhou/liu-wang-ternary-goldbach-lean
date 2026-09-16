import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightSeed

set_option autoImplicit false
noncomputable section

open Complex Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_right_cell_log_certificate
    {a l v qt ut : ℚ} (q u : ℕ → ℚ) (ha : 1 < a) (hu1 : u 1 = 1)
    (hterms : ∀ n : ℕ, 2 ≤ n → n ≤ 16 →
      0 ≤ q n ∧ 0 ≤ u n ∧ q n ≤ a * (logNaturalCenter n - 1 / 1000000) ∧
        1 ≤ u n * backlundExpLower (q n))
    (hqt : 0 ≤ qt) (hut : 0 ≤ ut)
    (htq : qt ≤ (a - 1) * (logNaturalCenter 16 - 1 / 1000000))
    (htp : 1 ≤ (a - 1) * ut * backlundExpLower qt)
    (hv : (∑ n ∈ range 16, u (n + 1)) + ut ≤ v)
    (hl : 0 ≤ l) (hlp : v ≤ backlundExpLower l) :
    Real.log (backlundDirichletEnvelope 16 (a : ℝ)) ≤ (l : ℝ) := by
  have haR : (1 : ℝ) < a := by exact_mod_cast ha
  have hm : (∑ n ∈ range 16, (n + 1 : ℝ) ^ (-(a : ℝ))) ≤
      ∑ n ∈ range 16, (u (n + 1) : ℝ) := by
    apply sum_le_sum
    intro n hn
    have hn16 : n < 16 := mem_range.mp hn
    by_cases hn0 : n = 0
    · subst n
      norm_num [hu1]
    · have hh := hterms (n + 1) (by omega) (by omega)
      have h := backlund_rpow_div_certificate (n := n + 1) (by omega) (by omega)
        (a := a) (q := q (n + 1)) (d := 1) (u := u (n + 1))
        (by linarith) hh.1 (by norm_num) hh.2.1 hh.2.2.1 (by simpa using hh.2.2.2)
      simpa only [Nat.cast_add, Nat.cast_one, Rat.cast_one, div_one] using h
  have ht := backlund_rpow_div_certificate (n := 16) (by norm_num) (by norm_num)
    (a := a - 1) (q := qt) (d := a - 1) (u := ut) (by linarith) hqt (by linarith)
    hut htq htp
  have ht' : (16 : ℝ) ^ (1 - (a : ℝ)) / ((a : ℝ) - 1) ≤ (ut : ℝ) := by
    simpa only [Rat.cast_sub, Rat.cast_one, neg_sub, Nat.cast_ofNat] using ht
  have hvR : (∑ n ∈ range 16, (u (n + 1) : ℝ)) + (ut : ℝ) ≤ (v : ℝ) := by
    simpa only [Rat.cast_add, Rat.cast_sum] using
      (Rat.cast_le.mpr hv : (((∑ n ∈ range 16, u (n + 1)) + ut : ℚ) : ℝ) ≤ (v : ℝ))
  apply backlund_log_certificate (backlundDirichletEnvelope_pos (by norm_num) haR) _ hl hlp
  unfold backlundDirichletEnvelope
  norm_num only [Nat.cast_ofNat]
  linarith

def backlundRightAngle (j : ℕ) : ℚ := (355 / 113) * j / 128

def backlundRightPhase (j : ℕ) : QComplex :=
  unitRepeatedSquare 7 (backlundRightAngle j / 128)

theorem backlund_right_cell_sigma {j : ℕ} (hj : j ≤ 64) {a : ℚ}
    (ha : a ≤ max (5 / 4) (5 / 4 + (33 / 25) *
      ((backlundRightPhase j).1 - (4 * 3 ^ 7 - 1) / 100000000)))
    {θ : ℝ} (hθ : 0 ≤ θ) (hθj : θ ≤ (j : ℝ) * Real.pi / 128) :
    (a : ℝ) ≤ 5 / 4 + (33 / 25 : ℝ) * Real.cos θ := by
  have hjR : (j : ℝ) ≤ 64 := by exact_mod_cast hj
  have hjQ : (j : ℚ) ≤ 64 := by exact_mod_cast hj
  have hp : Real.pi ≤ (355 / 113 : ℝ) := by linarith [Real.pi_lt_d20]
  have hang : (0 : ℝ) ≤ (backlundRightAngle j : ℝ) := by
    unfold backlundRightAngle
    positivity
  have hang' : (backlundRightAngle j : ℝ) ≤ Real.pi := by
    dsimp [backlundRightAngle]
    push_cast
    nlinarith [Real.pi_gt_three, Nat.cast_nonneg (α := ℝ) j]
  have hθa : θ ≤ (backlundRightAngle j : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    dsimp [backlundRightAngle]
    push_cast
    linarith
  have hθhalf : θ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθhalf⟩
  have hseed : |backlundRightAngle j / 128| ≤ (1 : ℚ) := by
    rw [abs_of_nonneg (by unfold backlundRightAngle; positivity)]
    unfold backlundRightAngle
    linarith
  have hphase := unitRepeatedSquare_error hseed (by norm_num : (7 : ℕ) ≤ 7)
  rw [show (2 : ℝ) ^ 7 = 128 by norm_num] at hphase
  have heq : (128 : ℝ) * ((backlundRightAngle j / 128 : ℚ) : ℝ) =
      (backlundRightAngle j : ℝ) := by push_cast; ring
  rw [heq] at hphase
  have hr := (abs_re_le_norm
    (Complex.exp ((backlundRightAngle j : ℝ) * I) - (backlundRightPhase j).toComplex)).trans hphase
  have hre : (Complex.exp ((backlundRightAngle j : ℝ) * I)).re =
      Real.cos (backlundRightAngle j : ℝ) := by
    norm_num only [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, add_re, mul_re,
      ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  simp only [sub_re, hre, QComplex.toComplex, add_re, mul_re, ratCast_re, ratCast_im,
    I_re, I_im, zero_mul, mul_zero, sub_zero, add_zero] at hr
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hθ hang' hθa
  have haR : (a : ℝ) ≤ max (5 / 4) (5 / 4 + (33 / 25 : ℝ) *
      (((backlundRightPhase j).1 : ℝ) - (4 * 3 ^ 7 - 1) / 100000000)) := by
    simpa only [Rat.cast_max, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using
      (Rat.cast_le.mpr ha : (a : ℝ) ≤
        ((max (5 / 4) (5 / 4 + (33 / 25) *
          ((backlundRightPhase j).1 - (4 * 3 ^ 7 - 1) / 100000000)) : ℚ) : ℝ))
  apply haR.trans
  apply max_le
  · nlinarith
  · nlinarith [(abs_le.mp hr).1]

#print axioms backlund_right_cell_log_certificate
#print axioms backlund_right_cell_sigma

end LiuWang.Proof.Campaign20260915.RosserCount
