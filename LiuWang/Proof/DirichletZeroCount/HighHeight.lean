import LiuWang.Proof.DirichletZeroCount.Main
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# An explicit high-height bound with the Riemann--von Mangoldt leading scale

The remaining linear and square-root smoothing losses are displayed, not
hidden in O notation. This is not claimed to imply companion Theorems 5/6.
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.DirichletZeroCount

theorem arctan_padding_lower {a : ℝ} (ha : 0 < a) :
    Real.pi / 2 - 2 / a ≤ Real.arctan (a / 2) := by
  have hu : 0 ≤ (a / 2)⁻¹ := by positivity
  have h := Real.le_tan (Real.arctan_nonneg.mpr hu)
    (Real.arctan_lt_pi_div_two ((a / 2)⁻¹))
  rw [Real.tan_arctan, Real.arctan_inv_of_pos (by positivity : 0 < a / 2)] at h
  have hi : (a / 2)⁻¹ = 2 / a := by ring
  rw [hi] at h
  linarith

theorem sqrt_padding_den_pos {y : ℝ} (hy : 16 ≤ y) :
    0 < Real.pi - 4 / Real.sqrt y := by
  have hs : 4 ≤ Real.sqrt y := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by norm_num; exact hy)
  have hd : 4 / Real.sqrt y ≤ 1 := (div_le_one (by linarith)).mpr hs
  linarith [Real.pi_gt_three]

theorem padding_quotient_le {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hd : 0 < Real.pi - 4 / a) :
    B / Real.arctan (a / 2) ≤ 2 * B / (Real.pi - 4 / a) := by
  have hl := arctan_padding_lower ha
  have hp : 0 < Real.arctan (a / 2) := Real.arctan_pos.mpr (by positivity)
  apply (div_le_div_iff₀ hp hd).mpr
  rw [show Real.pi - 4 / a = 2 * (Real.pi / 2 - 2 / a) by ring]
  nlinarith [mul_le_mul_of_nonneg_left hl hB]

theorem count_conductor_high {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (alpha : ℝ) {y : ℝ} (hy : 16 ≤ y) :
    (count chi alpha y : ℝ) ≤
      (y + Real.sqrt y) *
        (Real.log chi.conductor + Real.log (y + Real.sqrt y + 2) + 4) /
          (Real.pi - 4 / Real.sqrt y) := by
  have hy0 : 0 ≤ y := by linarith
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have hd := sqrt_padding_den_pos hy
  have hc := count_conductor_smoothed hchi alpha hy0 hs
  have hlogd : 0 ≤ Real.log chi.conductor :=
    Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero)
  have hlogy : 0 ≤ Real.log (y + Real.sqrt y + 2) :=
    Real.log_nonneg (by linarith)
  have hp := padding_quotient_le hs
    (B := (y + Real.sqrt y) *
      (Real.log chi.conductor / 2 + Real.log (y + Real.sqrt y + 2) / 2 + 2))
    (by positivity) hd
  exact hc.trans (hp.trans_eq (by ring))

theorem count_principal_high (q : ℕ) [NeZero q] (alpha : ℝ)
    {y : ℝ} (hy : 16 ≤ y) :
    (count (1 : Character q) alpha y : ℝ) ≤
      (y + Real.sqrt y) * (Real.log (y + Real.sqrt y + 2) + 14 / 3) /
        (Real.pi - 4 / Real.sqrt y) := by
  have hy0 : 0 ≤ y := by linarith
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have hlogy : 0 ≤ Real.log (y + Real.sqrt y + 2) :=
    Real.log_nonneg (by linarith)
  have hc := count_principal_smoothed q alpha hy0 hs
  have hp := padding_quotient_le hs
    (B := (y + Real.sqrt y) * (Real.log (y + Real.sqrt y + 2) / 2 + 7 / 3))
    (by positivity) (sqrt_padding_den_pos hy)
  exact hc.trans (hp.trans_eq (by ring))

end LiuWang.Proof.DirichletZeroCount
