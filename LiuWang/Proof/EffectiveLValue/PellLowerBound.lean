import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The explicit unit estimate in Liu--Wang (2.35)--(2.36)

These estimates apply to every positive integral solution of `v^2 - r*u^2 = 4`.
No existence of a fundamental unit, nor an identification with a regulator,
is assumed or claimed.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

def sourceUnitLower (r : ℝ) : ℝ :=
  (Real.sqrt (4 + r) + Real.sqrt r) / 2

theorem sourceUnitLower_le_pellUnit {r : ℝ} (hr : 0 ≤ r) {v u : ℤ}
    (hv : 0 < v) (hu : 0 < u) (hpell : (v : ℝ) ^ 2 - r * (u : ℝ) ^ 2 = 4) :
    sourceUnitLower r ≤ ((v : ℝ) + (u : ℝ) * Real.sqrt r) / 2 := by
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hv0 : (0 : ℝ) ≤ v := by exact_mod_cast hv.le
  have husq : (1 : ℝ) ≤ (u : ℝ) ^ 2 := by nlinarith
  have hvsq : 4 + r ≤ (v : ℝ) ^ 2 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr husq)]
  have hsv : Real.sqrt (4 + r) ≤ (v : ℝ) := (Real.sqrt_le_iff).mpr ⟨hv0, hvsq⟩
  have hsu : Real.sqrt r ≤ (u : ℝ) * Real.sqrt r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (Real.sqrt_nonneg r)]
  unfold sourceUnitLower
  linarith

theorem pi_lt_log_sourceUnitLower {r : ℝ} (hr : 987 ≤ r) :
    Real.pi < Real.log (sourceUnitLower r) := by
  have hs30 : (30 : ℝ) ≤ Real.sqrt r :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have hs30' : (30 : ℝ) ≤ Real.sqrt (4 + r) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have hlow : (30 : ℝ) ≤ sourceUnitLower r := by
    unfold sourceUnitLower
    linarith
  have hcube : (30 : ℝ) ^ 3 ≤ sourceUnitLower r ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hlow 3
  have hlog : Real.log (2 ^ (14 : ℕ) : ℝ) < Real.log (sourceUnitLower r ^ 3) := by
    apply Real.log_lt_log (by norm_num)
    linarith
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have htwo := Real.log_two_gt_d9
  have hpi := Real.pi_lt_d2
  nlinarith

theorem pi_lt_log_pellUnit {r : ℝ} (hr : 987 ≤ r) {v u : ℤ}
    (hv : 0 < v) (hu : 0 < u) (hpell : (v : ℝ) ^ 2 - r * (u : ℝ) ^ 2 = 4) :
    Real.pi < Real.log (((v : ℝ) + (u : ℝ) * Real.sqrt r) / 2) := by
  apply (pi_lt_log_sourceUnitLower hr).trans_le
  apply Real.log_le_log
  · unfold sourceUnitLower
    positivity
  · exact sourceUnitLower_le_pellUnit (by linarith) hv hu hpell

theorem source_minimum_eq_pi_div_sqrt {r : ℝ} (hr : 987 ≤ r) :
    min (Real.pi / Real.sqrt r) (Real.log (sourceUnitLower r) / Real.sqrt r) =
      Real.pi / Real.sqrt r := by
  apply min_eq_left
  exact div_le_div_of_nonneg_right (pi_lt_log_sourceUnitLower hr).le (Real.sqrt_nonneg r)

end LiuWang.Proof.EffectiveLValue
