import LiuWang.Proof.DirichletZeroCount.Remainder.UniformWeights
import LiuWang.Proof.DirichletZeroCount.SourceLow
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Paying the literal companion Theorem 6 from stronger actual count producers -/

set_option autoImplicit false
noncomputable section
open Complex
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def sixMain (q : ℕ) (y : ℝ) : ℝ :=
  y * Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ / (2 * Real.pi)) -
    y + (1 / 2) * Real.arctan (2 * y / 3)

theorem sourceSixBound_lower (q : ℕ) (y : ℝ) :
    (sixMain q y + Real.pi +
      7 * (Real.pi + 3) * (Real.log ((q : ℝ) * (2 + y)) / 2 + 0.59773) + 3.942) / Real.pi ≤
        sourceSixBound q y := by
  have hrec : 0 ≤ 1 / (4 * ‖(1 / 2 : ℂ) + (y : ℂ) * I‖) := by positivity
  have hlast : 0 ≤ 4 / Real.pi *
      (1.5 / (‖(0.5 : ℂ) + (y : ℂ) * I‖ * ‖(2 : ℂ) + (y : ℂ) * I‖)) := by positivity
  have he : sourceSixBound q y =
      (sixMain q y + Real.pi +
        7 * (Real.pi + 3) * (Real.log ((q : ℝ) * (2 + y)) / 2 + 0.59773) + 3.942) / Real.pi +
          1 / (4 * ‖(1 / 2 : ℂ) + (y : ℂ) * I‖) +
          4 / Real.pi * (1.5 / (‖(0.5 : ℂ) + (y : ℂ) * I‖ * ‖(2 : ℂ) + (y : ℂ) * I‖)) := by
    unfold sourceSixBound sixMain
    field_simp [Real.pi_ne_zero]
    ring
  rw [he]
  linarith

theorem parity_gamma_le_odd {q : ℕ} (chi : Character q) {y : ℝ} (hy : 0 ≤ y) :
    sourceGammaMain (parityShift chi) y ≤ sourceGammaMain (3 / 2) y := by
  unfold parityShift
  split_ifs
  · have hn : ‖((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I‖ ≤ ‖((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
      norm_num
    have hp : 0 < ‖((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I‖ :=
      lt_of_lt_of_le (by norm_num) (re_le_norm _)
    have hl := Real.log_le_log (div_pos hp (by norm_num))
      (div_le_div_of_nonneg_right hn (by norm_num : (0 : ℝ) ≤ 2))
    have ha := Real.arctan_nonneg.mpr (div_nonneg hy (by norm_num : (0 : ℝ) ≤ 1 / 2))
    have hb := Real.arctan_nonneg.mpr (div_nonneg hy (by norm_num : (0 : ℝ) ≤ 3 / 2))
    unfold sourceGammaMain
    nlinarith [mul_le_mul_of_nonneg_left hl hy]
  · exact le_rfl

theorem uniformCountBound_le_sixMain {q : ℕ} (hq : 0 < q) (chi : Character q)
    {y : ℝ} (hy : 0 ≤ y) :
    uniformCountBound q (parityShift chi) y ≤
      (sixMain q y + Real.pi + 2 * uniformHorizontalFee q y) / Real.pi := by
  have hn : 0 < ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ :=
    lt_of_lt_of_le (by norm_num) (re_le_norm _)
  have he : y * Real.log ((q : ℝ) / Real.pi) + sourceGammaMain (3 / 2) y = sixMain q y := by
    unfold sourceGammaMain sixMain
    push_cast
    have hqR : (q : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hq)
    rw [Real.log_div hqR Real.pi_ne_zero,
      Real.log_div hn.ne' (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div (mul_ne_zero hqR hn.ne') (mul_ne_zero (by norm_num) Real.pi_ne_zero),
      Real.log_mul hqR hn.ne', Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
    rw [show y / (3 / 2 : ℝ) = 2 * y / 3 by ring]
    ring
  unfold uniformCountBound
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  linarith [parity_gamma_le_odd chi hy]

theorem uniformCountBound_le_sourceSix_high {q : ℕ} (hq : 3 ≤ q) (chi : Character q)
    {y : ℝ} (hy : 10 / 3 ≤ y) :
    uniformCountBound q (parityShift chi) y ≤ sourceSixBound q y := by
  have hy0 : 0 ≤ y := by linarith
  have hq0 : 0 < q := by omega
  have hqR : (3 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hL : 11 / 4 ≤ Real.log ((q : ℝ) * (2 + y)) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
      (by nlinarith : 16 ≤ (q : ℝ) * (2 + y))
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_two_gt_d9]
  apply (uniformCountBound_le_sixMain hq0 chi hy0).trans
  apply le_trans _ (sourceSixBound_lower q y)
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have he : Real.log q + Real.log (|y| + 2) = Real.log ((q : ℝ) * (2 + y)) := by
    rw [Real.log_mul (Nat.cast_pos.mpr hq0).ne' (by positivity), abs_of_nonneg hy0, add_comm y 2]
  unfold uniformHorizontalFee
  have hh : (Real.pi - 3.14) * (Real.log ((q : ℝ) * (2 + y)) - 11 / 4) ≥ 0 :=
    mul_nonneg (by linarith [Real.pi_gt_d2]) (by linarith)
  nlinarith [Real.pi_lt_d2]

theorem log_modulus_ge_one {q : ℕ} (hq : 3 ≤ q) : 1 ≤ Real.log q := by
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (Nat.cast_le.mpr hq)
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have he : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  rw [he] at hm
  norm_num at hl
  linarith [Real.log_two_gt_d9]

theorem sourceSix_affine_lower {q : ℕ} (hq : 3 ≤ q) {y c m : ℝ}
    (hc : 0 ≤ c) (hL : Real.log q + c ≤ Real.log ((q : ℝ) * (2 + y)))
    (hm : m ≤ sixMain q y / Real.pi) :
    (34 / 5) * Real.log q + (34 / 5) * c + (68 / 5) * 0.59773 + 1 + 5 / 4 + m ≤
      sourceSixBound q y := by
  have hqlog := log_modulus_ge_one hq
  have hcoeff : 68 / 5 ≤ 7 * (1 + 3 / Real.pi) := by
    have hh : 33 / 35 ≤ 3 / Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d2])
    linarith
  have hnon : 0 ≤ Real.log ((q : ℝ) * (2 + y)) / 2 + 0.59773 := by linarith
  have hb := mul_le_mul_of_nonneg_right hcoeff hnon
  have hp : 5 / 4 ≤ 3.942 / Real.pi :=
    (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d2])
  have he : (sixMain q y + Real.pi +
      7 * (Real.pi + 3) * (Real.log ((q : ℝ) * (2 + y)) / 2 + 0.59773) + 3.942) / Real.pi =
        sixMain q y / Real.pi + 1 +
          7 * (1 + 3 / Real.pi) * (Real.log ((q : ℝ) * (2 + y)) / 2 + 0.59773) +
          3.942 / Real.pi := by field_simp
  have hh := sourceSixBound_lower q y
  rw [he] at hh
  linarith

theorem sixMain_small_lower {q : ℕ} (hq : 3 ≤ q) {y : ℝ} (hy : 0 ≤ y) (hy2 : y ≤ 2) :
    -1 ≤ sixMain q y / Real.pi := by
  have hqR : (3 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hn : (3 / 2 : ℝ) ≤ ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ := by
    simpa using re_le_norm ((3 / 2 : ℂ) + (y : ℂ) * I)
  have hr : 5 / 7 ≤ (q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ / (2 * Real.pi) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith [Real.pi_lt_d2])
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 5 / 7) hr
  have hb := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 7)
  norm_num at hb
  have hlog : -2 / 5 ≤ Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ / (2 * Real.pi)) :=
    by linarith
  have ha := Real.arctan_nonneg.mpr (by positivity : 0 ≤ 2 * y / 3)
  apply (le_div_iff₀ Real.pi_pos).mpr
  unfold sixMain
  nlinarith [mul_le_mul_of_nonneg_left hlog hy, Real.pi_gt_three]

theorem sixMain_middle_lower {q : ℕ} (hq : 3 ≤ q) {y : ℝ}
    (hy : 2 ≤ y) (hy3 : y ≤ 10 / 3) : -(4 / 3) ≤ sixMain q y / Real.pi := by
  have hqR : (3 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hn : 2 ≤ ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ := by
    have hh := im_le_norm ((3 / 2 : ℂ) + (y : ℂ) * I)
    norm_num at hh
    linarith
  have hr : 20 / 21 ≤ (q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ / (2 * Real.pi) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith [Real.pi_lt_d2])
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 20 / 21) hr
  have hb := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 20 / 21)
  norm_num at hb
  have hlog : -1 / 20 ≤ Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ / (2 * Real.pi)) :=
    by linarith
  have ha := Real.arctan_nonneg.mpr (by linarith : 0 ≤ 2 * y / 3)
  apply (le_div_iff₀ Real.pi_pos).mpr
  unfold sixMain
  nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ y), Real.pi_gt_three]

theorem log_small_height_upper {y : ℝ} (hy : 0 ≤ y) (hy3 : y ≤ 10 / 3) :
    Real.log (y + 3) ≤ 2 := by
  have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (y + 3) / 4)
  rw [Real.log_div (by positivity : y + 3 ≠ 0) (by norm_num : (4 : ℝ) ≠ 0),
    show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith [Real.log_two_lt_d9]

theorem count_le_sourceSix_small {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    {chi : Character q} (hchi : chi ≠ 1) (alpha : ℝ) {y : ℝ} (hy : 0 ≤ y) (hy3 : y ≤ 10 / 3) :
    (count chi alpha y : ℝ) ≤ sourceSixBound q y := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqlog := log_modulus_ge_one hq
  have hl := log_small_height_upper hy hy3
  have hrough {t : ℝ} (ht : y ≤ t) :
      nonprincipalBound q y ≤ (2 * t + 3) * (Real.log q / 2 + 9 / 4) := by
    unfold nonprincipalBound
    apply mul_le_mul (by linarith) (by linarith) _ (by linarith)
    have hh := Real.log_nonneg (by linarith : 1 ≤ y + 3)
    linarith
  have hlog {c : ℝ} (hc : c ≤ Real.log (2 + y)) :
      Real.log q + c ≤ Real.log ((q : ℝ) * (2 + y)) := by
    rw [Real.log_mul hq0.ne' (by positivity)]
    linarith
  apply (count_le_modulus hchi alpha hy).trans
  by_cases hy2 : y ≤ 2
  · have hl2 : 2 / 3 ≤ Real.log (2 + y) := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 + y)
      linarith [Real.log_two_gt_d9]
    have hb := sourceSix_affine_lower hq (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (hlog hl2) (sixMain_small_lower hq hy hy2)
    have hu := hrough hy2
    norm_num at hu
    linarith
  · have hy2' : 2 ≤ y := le_of_lt (lt_of_not_ge hy2)
    have hm := sixMain_middle_lower hq hy2' hy3
    by_cases hy3' : y ≤ 3
    · have hl4 : 4 / 3 ≤ Real.log (2 + y) := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : 4 ≤ 2 + y)
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hh
        norm_num only [Nat.cast_ofNat] at hh
        linarith [Real.log_two_gt_d9]
      have hb := sourceSix_affine_lower hq (by norm_num : (0 : ℝ) ≤ 4 / 3) (hlog hl4) hm
      have hu := hrough hy3'
      norm_num at hu
      linarith
    · have hl5 : 19 / 12 ≤ Real.log (2 + y) := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 5) (by linarith : 5 ≤ 2 + y)
        have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
        have he : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
          rw [show (5 : ℝ) = 2 ^ (2 : ℕ) * (5 / 4) by norm_num,
            Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
          norm_num
        rw [he] at hh
        norm_num at ht
        linarith [Real.log_two_gt_d9]
      have hb := sourceSix_affine_lower hq (by norm_num : (0 : ℝ) ≤ 19 / 12) (hlog hl5) hm
      have hu := hrough hy3
      norm_num at hu
      linarith

theorem count_nonprincipal_le_sourceSix_modulus {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤ sourceSixBound q y := by
  have hq := (BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hchi).trans
    (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)
  by_cases hys : y ≤ 10 / 3
  · exact count_le_sourceSix_small hq hchi alpha hy hys
  · exact (count_nonprincipal_uniform_modulus hchi ha hy).trans
      (uniformCountBound_le_sourceSix_high hq chi (le_of_lt (lt_of_not_ge hys)))

theorem count_nonprincipal_le_sourceSix_conductor {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤ sourceSixBound chi.conductor y := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [count_eq_primitive chi hchi]
  exact count_nonprincipal_le_sourceSix_modulus
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi) ha hy

end LiuWang.Proof.DirichletZeroCount.Remainder
