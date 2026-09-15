import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.Consumers

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap

theorem original_log_lower {x : ℝ} (hx : 8000000000 ≤ x) :
    22.8027 < Real.log x := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 8000000000) hx
  have he : (8000000000 : ℝ) = 2 ^ 12 * 5 ^ 9 := by norm_num
  rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

theorem original_radical_bounds :
    stechkinConductorCoeff ≤ 0.276393203 ∧ Real.sqrt 3 < 1.732050808 := by
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h5lower : (2.23606797 : ℝ) ≤ Real.sqrt 5 := by
    nlinarith [Real.sqrt_nonneg 5]
  have hk : stechkinK = Real.sqrt 5 / 5 := by
    unfold stechkinK
    apply (div_eq_div_iff (Real.sqrt_pos.mpr (by norm_num)).ne' (by norm_num)).mpr
    nlinarith only [h5]
  constructor
  · unfold stechkinConductorCoeff
    rw [hk]
    linarith only [h5lower]
  · nlinarith [Real.sqrt_nonneg 3]

theorem original_parameter_margin {x : ℝ} (hx : 8000000000 ≤ x) :
    0.26213 * (7 * stechkinConductorCoeff + 2.4998 / Real.log x) <
      (Real.sqrt 3 - 1) ^ 2 := by
  have hL := original_log_lower hx
  have hL0 : 0 < Real.log x := by linarith
  have hfrac : (2.4998 : ℝ) / Real.log x ≤ 2.4998 / 22.8027 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL.le
  have hfinite : (0.26213 : ℝ) * (7 * 0.276393203 + 2.4998 / 22.8027) <
      4 - 2 * 1.732050808 := by norm_num
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith [original_radical_bounds.1, original_radical_bounds.2]

theorem original_denominator_pos {x : ℝ} (hx : 8000000000 ≤ x) :
    0 < 7 * stechkinConductorCoeff + 2.4998 / Real.log x := by
  have hL : 0 < Real.log x := by linarith [original_log_lower hx]
  have hk := lwd_kappa_bounds.1
  positivity

theorem original_normalized_negative {x : ℝ} (hx : 8000000000 ≤ x) :
    1 / lwdSourceA x - 3 / (lwdSourceA x + 0.26213) +
      (7 * stechkinConductorCoeff + 2.4998 / Real.log x) < 0 := by
  let B := 7 * stechkinConductorCoeff + 2.4998 / Real.log x
  have hB : 0 < B := original_denominator_pos hx
  have ha : 0 < lwdSourceA x := (lwd_source_parameters hx).1
  have hac : 0 < lwdSourceA x + 0.26213 := by linarith
  have hab : lwdSourceA x * B = Real.sqrt 3 - 1 := by
    dsimp [lwdSourceA, B]
    exact div_mul_cancel₀ _ hB.ne'
  have hm : 0.26213 * B < (Real.sqrt 3 - 1) ^ 2 := original_parameter_margin hx
  have hroot := Real.sqrt_nonneg 3
  have hroot2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hroot1 : 1 < Real.sqrt 3 := by nlinarith
  have hprod : Real.sqrt 3 * (lwdSourceA x + 0.26213) < 3 * lwdSourceA x := by
    have hm' : 0.26213 * B < 4 - 2 * Real.sqrt 3 := by nlinarith only [hm, hroot2]
    have hh := mul_lt_mul_of_pos_left hm' (by linarith : 0 < Real.sqrt 3)
    have he : (3 * lwdSourceA x - Real.sqrt 3 * (lwdSourceA x + 0.26213)) * B =
        4 * Real.sqrt 3 - 6 - Real.sqrt 3 * (0.26213 * B) := by
      calc
        _ = (3 - Real.sqrt 3) * (lwdSourceA x * B) - Real.sqrt 3 * (0.26213 * B) := by ring
        _ = _ := by rw [hab]; nlinarith only [hroot2]
    have hnum : 0 < (3 * lwdSourceA x - Real.sqrt 3 * (lwdSourceA x + 0.26213)) * B := by
      nlinarith only [hh, he, hroot2]
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hB).mp hnum)
  have hcompare : 1 / lwdSourceA x + B < 3 / (lwdSourceA x + 0.26213) := by
    apply (lt_div_iff₀ hac).mpr
    have he : (1 / lwdSourceA x + B) * (lwdSourceA x + 0.26213) =
        Real.sqrt 3 * (lwdSourceA x + 0.26213) / lwdSourceA x := by
      field_simp
      nlinarith only [hab]
    rw [he]
    exact (div_lt_iff₀ ha).mpr (by nlinarith only [hprod])
  change 1 / lwdSourceA x - 3 / (lwdSourceA x + 0.26213) + B < 0
  linarith only [hcompare]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap
