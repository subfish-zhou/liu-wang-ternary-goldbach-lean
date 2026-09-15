import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalEvaluation
import LiuWang.Proof.Campaign20260915.ZetaValidation.SecondOrderEvaluation

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def halfZetaSecondLower (m D : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (m ^ 2), reciprocalSqrtLower (j + 1) D) -
    2 * (m : ℚ) - 1 / (2 * m) - 1 / (16 * m ^ 3)

def halfZetaSecondUpper (m D : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (m ^ 2), reciprocalSqrtUpper (j + 1) D) -
    2 * (m : ℚ) - 1 / (2 * m) + 1 / (16 * m ^ 3)

noncomputable section

open Complex

theorem halfZeta_second_error {m : ℕ} (hm : 1 ≤ m) :
    |normalizedCriticalZeta 0 -
      ((∑ j ∈ Finset.range (m ^ 2), 1 / Real.sqrt (j + 1 : ℝ)) -
        2 * (m : ℝ) - 1 / (2 * m))| ≤ 1 / (16 * (m : ℝ) ^ 3) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hN : 1 ≤ m ^ 2 := pow_pos (lt_of_lt_of_le Nat.zero_lt_one hm) _
  have hNp : (0 : ℝ) < (m ^ 2 : ℕ) := by exact_mod_cast hN
  have hs : Real.sqrt (m ^ 2 : ℕ) = (m : ℝ) := by
    push_cast
    exact Real.sqrt_sq hmR.le
  have hr : ((m ^ 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) - 1) = 1 / (m : ℝ) ^ 3 := by
    rw [sub_eq_add_neg, Real.rpow_add hNp, Real.rpow_neg hNp.le,
      ← Real.sqrt_eq_rpow, hs, Real.rpow_neg hNp.le, Real.rpow_one]
    push_cast
    field_simp
  have hp : criticalPoint 0 = ((1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> norm_num [criticalPoint]
  have hn : ‖criticalPoint 0‖ = (1 / 2 : ℝ) := by rw [hp]; norm_num
  have hn1 : ‖criticalPoint 0 + 1‖ = (3 / 2 : ℝ) := by rw [hp]; norm_num
  have he := norm_zeta_sub_abelApprox_second_le (s := criticalPoint 0)
    (by norm_num [criticalPoint]) (criticalPoint_ne_one 0) hN
  change ‖riemannZeta (criticalPoint 0) - abelApprox (criticalPoint 0) (m ^ 2)‖ ≤
    ‖criticalPoint 0‖ * ‖criticalPoint 0 + 1‖ *
      ((m ^ 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) - 1) / (8 * (1 / 2 + 1)) at he
  rw [hr, hn, hn1] at he
  have hb := (abs_re_le_norm
    (riemannZeta (criticalPoint 0) - abelApprox (criticalPoint 0) (m ^ 2))).trans he
  rw [sub_re, ← normalizedCriticalZeta_zero_eq, abelApprox_half_re hN, hs] at hb
  convert hb using 1
  all_goals first | rfl | ring

theorem halfZeta_second_rational_enclosure {m D : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D) :
    (halfZetaSecondLower m D : ℝ) ≤ normalizedCriticalZeta 0 ∧
      normalizedCriticalZeta 0 ≤ (halfZetaSecondUpper m D : ℝ) := by
  have he := abs_le.mp (halfZeta_second_error hm)
  have hl :
      (∑ j ∈ Finset.range (m ^ 2), (reciprocalSqrtLower (j + 1) D : ℝ)) ≤
        ∑ j ∈ Finset.range (m ^ 2), 1 / Real.sqrt (j + 1 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast (reciprocalSqrt_enclosure (n := j + 1) (by omega) hD).1
  have hu :
      (∑ j ∈ Finset.range (m ^ 2), 1 / Real.sqrt (j + 1 : ℝ)) ≤
        ∑ j ∈ Finset.range (m ^ 2), (reciprocalSqrtUpper (j + 1) D : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast (reciprocalSqrt_enclosure (n := j + 1) (by omega) hD).2
  dsimp [halfZetaSecondLower, halfZetaSecondUpper]
  push_cast
  constructor <;> linarith [he.1, he.2]

theorem endpoint_zero_second_enclosure :
    -(147 / 100 : ℝ) ≤ normalizedCriticalZeta 0 ∧
      normalizedCriticalZeta 0 ≤ -(29 / 20 : ℝ) := by
  have h := halfZeta_second_rational_enclosure (m := 4) (D := 1000)
    (by norm_num) (by norm_num)
  have hl : -(147 / 100 : ℚ) ≤ halfZetaSecondLower 4 1000 := by
    norm_num [halfZetaSecondLower, reciprocalSqrtLower, Finset.sum_range_succ]
  have hu : halfZetaSecondUpper 4 1000 ≤ -(29 / 20 : ℚ) := by
    norm_num [halfZetaSecondUpper, reciprocalSqrtUpper, Finset.sum_range_succ]
  have hlR : ((-(147 / 100) : ℚ) : ℝ) ≤ (halfZetaSecondLower 4 1000 : ℝ) := Rat.cast_le.mpr hl
  have huR : (halfZetaSecondUpper 4 1000 : ℝ) ≤ ((-(29 / 20) : ℚ) : ℝ) := Rat.cast_le.mpr hu
  norm_num at hlR huR
  exact ⟨hlR.trans h.1, h.2.trans huR⟩

#print axioms halfZeta_second_error
#print axioms halfZeta_second_rational_enclosure
#print axioms endpoint_zero_second_enclosure

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
