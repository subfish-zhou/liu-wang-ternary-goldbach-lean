import LiuWang.Proof.VaughanEstimate.Consumer

/-! 连续分母闭区间上的端点付款，保留随 N 衰减的母界。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.VaughanRecovery

open Interfaces Parameters ParameterComparisons VaughanTypeIIBudget

def tailRatio (N : ℕ) : ℝ :=
  sourceL N ^ ((13 : ℝ) / 2) / (N : ℝ) ^ ((1 : ℝ) / 2)

def middleRatio (N : ℕ) : ℝ :=
  sourceL N ^ ((12 : ℝ) / 5) / (N : ℝ) ^ ((1 : ℝ) / 5)

def mother (N : ℕ) (A B C : ℝ) : ℝ :=
  ((N : ℝ) / sourceL N) * (A + B * middleRatio N + C * tailRatio N)

theorem variable_pair_le {N : ℕ} {q A C : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ q) (hqU : q ≤ sourceQ N)
    (hC : 0 ≤ C) (hCA : C ≤ A) :
    A * (N : ℝ) * q ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      C * (N : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) ≤
      ((N : ℝ) / sourceL N) * (A + C * tailRatio N) := by
  have hL := sourceL_pos hN
  have hNp := natCast_pos_of_exp_le hN
  have hqp := (sourceP1_pos hN).trans_le hqL
  have hH := Real.rpow_pos_of_pos hNp ((1 : ℝ) / 2)
  have hNhalf : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast hNp.le]
    norm_num
  have hsplit : sourceL N ^ ((13 : ℝ) / 2) =
      sourceL N ^ ((7 : ℝ) / 2) * sourceL N ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (sourceL N) 3, ← Real.rpow_add hL]
    norm_num
  have hcoeff : sourceL N ^ ((13 : ℝ) / 2) =
      sourceL N ^ ((5 : ℝ) / 2) * sourceL N ^ (3 : ℕ) * sourceL N := by
    rw [hsplit]
    have he : sourceL N ^ ((7 : ℝ) / 2) =
        sourceL N ^ ((5 : ℝ) / 2) * sourceL N := by
      rw [← Real.rpow_add_one hL.ne']
      norm_num
    rw [he]
    ring
  have hleft : sourceL N ^ (3 : ℕ) ≤ q ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (sourceP1_pos hN).le hqL
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    unfold sourceP1 at h
    rw [← Real.rpow_natCast_mul hL.le] at h
    norm_num at h
    exact h
  have hright : q ^ ((1 : ℝ) / 2) ≤
      (N : ℝ) ^ ((1 : ℝ) / 2) / sourceL N ^ ((7 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow hqp.le hqU (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [sourceQ_eq_div, Real.div_rpow hNp.le (pow_nonneg hL.le _),
      ← Real.rpow_natCast_mul hL.le] at h
    norm_num at h
    exact h
  let t := q ^ ((1 : ℝ) / 2) / sourceL N ^ (3 : ℕ)
  have hR : 0 < tailRatio N := by unfold tailRatio; positivity
  have hR1 : tailRatio N ≤ 1 := (sourceL_thirteen_halves_ratio_le hN).trans (by norm_num)
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (pow_pos hL 3)).2
    simpa using hleft
  have htu : t ≤ 1 / tailRatio N := by
    dsimp [t, tailRatio]
    rw [one_div_div, hsplit, ← div_div]
    exact div_le_div_of_nonneg_right hright (pow_nonneg hL.le _)
  have hp : A / t + C * tailRatio N * t ≤ A + C * tailRatio N := by
    apply inverse_linear_le_of_endpoints (l := 1) (u := 1 / tailRatio N)
      (mul_nonneg hC hR.le) (by norm_num) ht htu
    · simp
    · have he : A / (1 / tailRatio N) + C * tailRatio N * (1 / tailRatio N) =
          A * tailRatio N + C := by field_simp
      rw [he]
      nlinarith [mul_nonneg (sub_nonneg.mpr hCA) (sub_nonneg.mpr hR1)]
  have hfirst :
      A * (N : ℝ) * q ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) =
        ((N : ℝ) / sourceL N) * (A / t) := by
    rw [show (-1 : ℝ) / 2 = -(1 / 2) by norm_num, Real.rpow_neg hqp.le]
    dsimp [t]
    field_simp
  have hthird :
      C * (N : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) =
        ((N : ℝ) / sourceL N) * (C * tailRatio N * t) := by
    dsimp [tailRatio, t]
    rw [hcoeff]
    field_simp
    rw [hNhalf]
  rw [hfirst, hthird, ← mul_add]
  exact mul_le_mul_of_nonneg_left hp (div_pos hNp hL).le

theorem termB_normalized {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    termB N = ((N : ℝ) / sourceL N) * middleRatio N := by
  have hL := sourceL_pos hN
  have hNp := natCast_pos_of_exp_le hN
  have hNpow : (N : ℝ) ^ ((4 : ℝ) / 5) * (N : ℝ) ^ ((1 : ℝ) / 5) =
      (N : ℝ) := by rw [← Real.rpow_add hNp]; norm_num
  have hLpow : sourceL N ^ ((7 : ℝ) / 5) * sourceL N =
      sourceL N ^ ((12 : ℝ) / 5) := by
    rw [← Real.rpow_add_one hL.ne']; norm_num
  unfold termB middleRatio
  rw [← hLpow]
  field_simp
  exact hNpow

theorem tail_normalized {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ((N : ℝ) / sourceL N) * tailRatio N =
      (N : ℝ) ^ ((1 : ℝ) / 2) * sourceL N ^ ((11 : ℝ) / 2) := by
  have hL := sourceL_pos hN
  have hNp := natCast_pos_of_exp_le hN
  have hH := Real.rpow_pos_of_pos hNp ((1 : ℝ) / 2)
  have hNhalf : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast hNp.le]
    norm_num
  have hcoeff : sourceL N ^ ((13 : ℝ) / 2) =
      sourceL N ^ ((11 : ℝ) / 2) * sourceL N := by
    rw [← Real.rpow_add_one hL.ne']
    norm_num
  unfold tailRatio
  rw [hcoeff]
  field_simp
  nlinarith only [hNhalf]

theorem mother_eq {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (A B C : ℝ) :
    mother N A B C =
      A * (N : ℝ) / sourceL N + B * termB N +
        C * (N : ℝ) ^ ((1 : ℝ) / 2) * sourceL N ^ ((11 : ℝ) / 2) := by
  unfold mother
  rw [mul_add, mul_add, ← mul_assoc _ C, mul_right_comm _ C, tail_normalized hN,
    ← mul_assoc _ B, mul_right_comm _ B, ← termB_normalized hN]
  ring

theorem continuous_three_terms_le_mother {N : ℕ} {q A B C : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ q) (hqU : q ≤ sourceQ N)
    (hC : 0 ≤ C) (hCA : C ≤ A) :
    A * (N : ℝ) * q ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      B * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
      C * (N : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) ≤ mother N A B C := by
  have hp := variable_pair_le hN hqL hqU hC hCA
  have hb : B * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) =
      ((N : ℝ) / sourceL N) * (B * middleRatio N) := by
    calc
      _ = B * termB N := by unfold termB; ring
      _ = _ := by rw [termB_normalized hN]; ring
  rw [hb]
  unfold mother
  linarith

theorem three_terms_le_mother {N q : ℕ} {A B C : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hC : 0 ≤ C) (hCA : C ≤ A) :
    A * termA N q + B * termB N + C * termC N q ≤ mother N A B C := by
  simpa only [termA, termB, termC, mul_assoc] using
    continuous_three_terms_le_mother hN hqL hqU hC hCA

theorem tailRatio_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    tailRatio N ≤ 1 / 3100 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have hp : sourceL N ^ ((13 : ℝ) / 2) ≤ sourceL N ^ (7 : ℕ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (one_le_sourceL hn)
      (show (13 : ℝ) / 2 ≤ 7 by norm_num)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (natCast_pos_of_exp_le hn) _)).2
  have hs : 3100 * sourceL N ^ ((13 : ℝ) / 2) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    calc
      _ ≤ 3100 * sourceL N ^ (7 : ℕ) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ sourceL N * sourceL N ^ (7 : ℕ) :=
        mul_le_mul_of_nonneg_right (sourceL_ge_3100 hN) (by positivity)
      _ = sourceL N ^ (8 : ℕ) := by ring
      _ ≤ _ := (sourceL_eighth_lt_natCast_half hn).le
  linarith

theorem middleRatio_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    middleRatio N ≤ 1 / 50000 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have hp : sourceL N ^ ((12 : ℝ) / 5) ≤ sourceL N ^ ((5 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_sourceL hn) (by norm_num)
  have hs : 50 ≤ sourceL N ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.le_sqrt (by norm_num) hL.le).2
    linarith [sourceL_ge_3100 hN]
  have hm := mul_le_mul hs hp (Real.rpow_nonneg hL.le _) (by positivity)
  rw [← Real.rpow_add hL] at hm
  norm_num at hm
  have hsmall := thousand_mul_cube_lt_exp_fifth (sourceL_ge_2000 hn)
  have he : (N : ℝ) ^ ((1 : ℝ) / 5) = Real.exp (sourceL N / 5) := by
    rw [Real.rpow_def_of_pos (natCast_pos_of_exp_le hn)]
    congr 1
    unfold sourceL
    ring
  unfold middleRatio
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (natCast_pos_of_exp_le hn) _)).2
  rw [he]
  linarith

theorem mother_le_uniform {N : ℕ} {A B C D : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hpay : A + B / 50000 + C / 3100 ≤ D) :
    mother N A B C ≤ D * (N : ℝ) / sourceL N := by
  have hb := mul_le_mul_of_nonneg_left (middleRatio_le hN) hB
  have hc := mul_le_mul_of_nonneg_left (tailRatio_le hN) hC
  have hp : A + B * middleRatio N + C * tailRatio N ≤ D := by linarith
  have hn := exp_2000_le_of_exp_3100_le hN
  calc
    _ ≤ ((N : ℝ) / sourceL N) * D :=
      mul_le_mul_of_nonneg_left hp (div_pos (natCast_pos_of_exp_le hn) (sourceL_pos hn)).le
    _ = _ := by ring

theorem continuous_three_terms_le_uniform {N : ℕ} {q A B C D : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ q) (hqU : q ≤ sourceQ N)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hCA : C ≤ A)
    (hpay : A + B / 50000 + C / 3100 ≤ D) :
    A * (N : ℝ) * q ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      B * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
      C * (N : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) ≤ D * (N : ℝ) / sourceL N :=
  (continuous_three_terms_le_mother (exp_2000_le_of_exp_3100_le hN) hqL hqU hC hCA).trans
    (mother_le_uniform hN hB hC hpay)

end LiuWang.Proof.VaughanRecovery
