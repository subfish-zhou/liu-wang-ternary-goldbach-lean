import LiuWang.Proof.SmallConductorExpansion.Tables

/-!
# All nonprincipal quadratic characters modulo eight

The two independent unit values at 3 and 5 enumerate all four quadratic
characters. Nonprincipality eliminates the all-one case; all other cases
receive exact signed certificates, including the negative-prefix even case.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def eightValues (a b : ℤ) : List ℤ := [0, 1, 0, a, 0, b, 0, a * b]

theorem eight_table (chi : DirichletCharacter ℂ 8)
    {a b : ℤ} (ha : chi 3 = (a : ℂ)) (hb : chi 5 = (b : ℂ)) :
    ∀ z : ZMod 8, chi z = ((eightValues a b).getD z.val 0 : ℂ) := by
  have hz : chi 0 = 0 := MulChar.map_nonunit chi (by decide : ¬IsUnit (0 : ZMod 8))
  have h2 : chi 2 = 0 := MulChar.map_nonunit chi (by decide : ¬IsUnit (2 : ZMod 8))
  have h4 : chi 4 = 0 := MulChar.map_nonunit chi (by decide : ¬IsUnit (4 : ZMod 8))
  have h6 : chi 6 = 0 := MulChar.map_nonunit chi (by decide : ¬IsUnit (6 : ZMod 8))
  have h7 : chi 7 = (a * b : ℤ) := by
    rw [show (7 : ZMod 8) = 3 * 5 by decide, map_mul, ha, hb, Int.cast_mul]
  intro z
  fin_cases z
  · change chi 0 = (0 : ℤ)
    simpa using hz
  · change chi 1 = (1 : ℤ)
    simp
  · change chi 2 = (0 : ℤ)
    simpa using h2
  · exact ha
  · change chi 4 = (0 : ℤ)
    simpa using h4
  · exact hb
  · change chi 6 = (0 : ℤ)
    simpa using h6
  · exact h7

theorem eight_values_classified (chi : DirichletCharacter ℂ 8) (hc : chi ≠ 1)
    (hsq : chi ^ 2 = 1) :
    (chi 3 = -1 ∧ chi 5 = -1) ∨
      (chi 3 = 1 ∧ chi 5 = -1) ∨ (chi 3 = -1 ∧ chi 5 = 1) := by
  have h3 := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq (3 : ZMod 8)
  have h5 := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq (5 : ZMod 8)
  have h3z : chi 3 ≠ 0 := ((show IsUnit (3 : ZMod 8) by decide).map chi).ne_zero
  have h5z : chi 5 ≠ 0 := ((show IsUnit (5 : ZMod 8) by decide).map chi).ne_zero
  rcases h3 with h3 | h3 | h3
  · exact (h3z h3).elim
  · rcases h5 with h5 | h5 | h5
    · exact (h5z h5).elim
    · have ht := eight_table chi (a := 1) (b := 1) (by simpa using h3) (by simpa using h5)
      have hp := DirichletLWeakStripDerivative.sum_one_period_eq_zero chi hc
      norm_num [Finset.sum_range_succ, ht, eightValues] at hp
    · exact Or.inr (Or.inl ⟨h3, h5⟩)
  · rcases h5 with h5 | h5 | h5
    · exact (h5z h5).elim
    · exact Or.inr (Or.inr ⟨h3, h5⟩)
    · exact Or.inl ⟨h3, h5⟩

theorem eight_even_certificate : RationalCertificate 8 (eightValues (-1) (-1)) 32 1 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, eightValues, Finset.sum_range_succ]

theorem eight_odd_certificate : RationalCertificate 8 (eightValues 1 (-1)) 32 2 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, eightValues, Finset.sum_range_succ]

theorem eight_imprimitive_certificate : RationalCertificate 8 (eightValues (-1) 1) 32 1 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, eightValues, Finset.sum_range_succ]

theorem quadratic_eight_original_region (chi : DirichletCharacter ℂ 8)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rcases eight_values_classified chi hc hsq with ⟨h3, h5⟩ | ⟨h3, h5⟩ | ⟨h3, h5⟩
  · exact rationalCertificate_original_region chi hc (eightValues (-1) (-1))
      (eight_table chi (by simpa using h3) (by simpa using h5))
      (by decide) (by decide) eight_even_certificate hx hb
  · exact rationalCertificate_original_region chi hc (eightValues 1 (-1))
      (eight_table chi (by simpa using h3) (by simpa using h5))
      (by decide) (by decide) eight_odd_certificate hx hb
  · exact rationalCertificate_original_region chi hc (eightValues (-1) 1)
      (eight_table chi (by simpa using h3) (by simpa using h5))
      (by decide) (by decide) eight_imprimitive_certificate hx hb

end LiuWang.Proof.SmallConductorExpansion
