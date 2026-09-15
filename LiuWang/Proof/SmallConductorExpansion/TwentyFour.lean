import LiuWang.Proof.SmallConductorExpansion.Tables

/-! # Exhaustive three-sign classification of quadratic characters modulo 24 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def valuesTwentyFour (a b c : ℤ) : List ℤ :=
  [0, 1, 0, 0, 0, a, 0, b, 0, 0, 0, a * b, 0, c, 0, 0,
    0, a * c, 0, b * c, 0, 0, 0, a * b * c]

theorem twentyfour_table (chi : DirichletCharacter ℂ 24) {a b c : ℤ}
    (ha : chi 5 = (a : ℂ)) (hb : chi 7 = (b : ℂ)) (hc : chi 13 = (c : ℂ)) :
    ∀ z : ZMod 24, chi z = ((valuesTwentyFour a b c).getD z.val 0 : ℂ) := by
  intro z
  fin_cases z
  · change chi (0 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (0 : ZMod 24))]
    norm_num
  · change chi (1 : ZMod 24) = ((1 : ℤ) : ℂ)
    rw [show (1 : ZMod 24) = 5 ^ 0 * 7 ^ 0 * 13 ^ 0 by decide]
    simp_all
  · change chi (2 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (2 : ZMod 24))]
    norm_num
  · change chi (3 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (3 : ZMod 24))]
    norm_num
  · change chi (4 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (4 : ZMod 24))]
    norm_num
  · change chi (5 : ZMod 24) = ((a : ℤ) : ℂ)
    rw [show (5 : ZMod 24) = 5 ^ 1 * 7 ^ 0 * 13 ^ 0 by decide]
    simp_all
  · change chi (6 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (6 : ZMod 24))]
    norm_num
  · change chi (7 : ZMod 24) = ((b : ℤ) : ℂ)
    rw [show (7 : ZMod 24) = 5 ^ 0 * 7 ^ 1 * 13 ^ 0 by decide]
    simp_all
  · change chi (8 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (8 : ZMod 24))]
    norm_num
  · change chi (9 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (9 : ZMod 24))]
    norm_num
  · change chi (10 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (10 : ZMod 24))]
    norm_num
  · change chi (11 : ZMod 24) = ((a * b : ℤ) : ℂ)
    rw [show (11 : ZMod 24) = 5 ^ 1 * 7 ^ 1 * 13 ^ 0 by decide]
    simp_all
  · change chi (12 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (12 : ZMod 24))]
    norm_num
  · change chi (13 : ZMod 24) = ((c : ℤ) : ℂ)
    rw [show (13 : ZMod 24) = 5 ^ 0 * 7 ^ 0 * 13 ^ 1 by decide]
    simp_all
  · change chi (14 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (14 : ZMod 24))]
    norm_num
  · change chi (15 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (15 : ZMod 24))]
    norm_num
  · change chi (16 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (16 : ZMod 24))]
    norm_num
  · change chi (17 : ZMod 24) = ((a * c : ℤ) : ℂ)
    rw [show (17 : ZMod 24) = 5 ^ 1 * 7 ^ 0 * 13 ^ 1 by decide]
    simp_all
  · change chi (18 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (18 : ZMod 24))]
    norm_num
  · change chi (19 : ZMod 24) = ((b * c : ℤ) : ℂ)
    rw [show (19 : ZMod 24) = 5 ^ 0 * 7 ^ 1 * 13 ^ 1 by decide]
    simp_all
  · change chi (20 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (20 : ZMod 24))]
    norm_num
  · change chi (21 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (21 : ZMod 24))]
    norm_num
  · change chi (22 : ZMod 24) = ((0 : ℤ) : ℂ)
    rw [MulChar.map_nonunit chi (by decide : ¬IsUnit (22 : ZMod 24))]
    norm_num
  · change chi (23 : ZMod 24) = ((a * b * c : ℤ) : ℂ)
    rw [show (23 : ZMod 24) = 5 ^ 1 * 7 ^ 1 * 13 ^ 1 by decide]
    simp_all

theorem twentyfour_certificate0 :
    RationalCertificate 24 (valuesTwentyFour (-1) (-1) (-1)) 32 1 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, valuesTwentyFour, Finset.sum_range_succ]

theorem twentyfour_certificate1 :
    RationalCertificate 24 (valuesTwentyFour (-1) (-1) (1)) 32 1 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, valuesTwentyFour, Finset.sum_range_succ]

theorem twentyfour_certificate2 :
    RationalCertificate 24 (valuesTwentyFour (-1) (1) (-1)) 32 1 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, valuesTwentyFour, Finset.sum_range_succ]

theorem twentyfour_certificate3 :
    RationalCertificate 24 (valuesTwentyFour (-1) (1) (1)) 32 1 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, valuesTwentyFour, Finset.sum_range_succ]

theorem twentyfour_certificate4 :
    RationalCertificate 24 (valuesTwentyFour (1) (-1) (-1)) 32 2 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, valuesTwentyFour, Finset.sum_range_succ]

theorem twentyfour_certificate5 :
    RationalCertificate 24 (valuesTwentyFour (1) (-1) (1)) 32 2 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, valuesTwentyFour, Finset.sum_range_succ]

theorem twentyfour_certificate6 :
    RationalCertificate 24 (valuesTwentyFour (1) (1) (-1)) 32 4 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, valuesTwentyFour, Finset.sum_range_succ]

theorem twentyfour_certificate7 :
    RationalCertificate 24 (valuesTwentyFour (1) (1) (1)) 32 8 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, valuesTwentyFour, Finset.sum_range_succ]

theorem quadratic_twentyfour_original_region (chi : DirichletCharacter ℂ 24)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have hsign (z : ZMod 24) (hu : IsUnit z) : chi z = -1 ∨ chi z = 1 := by
    have hz : chi z ≠ 0 := (hu.map chi).ne_zero
    exact ((MulChar.isQuadratic_iff_sq_eq_one.mpr hsq z).resolve_left hz).symm
  rcases hsign 5 (by decide) with h5 | h5 <;>
    rcases hsign 7 (by decide) with h7 | h7 <;>
      rcases hsign 13 (by decide) with h13 | h13
  · exact rationalCertificate_original_region chi hc (valuesTwentyFour (-1) (-1) (-1))
      (twentyfour_table chi (by simpa using h5) (by simpa using h7) (by simpa using h13))
      (by decide) (by decide) twentyfour_certificate0 hx hb
  · exact rationalCertificate_original_region chi hc (valuesTwentyFour (-1) (-1) (1))
      (twentyfour_table chi (by simpa using h5) (by simpa using h7) (by simpa using h13))
      (by decide) (by decide) twentyfour_certificate1 hx hb
  · exact rationalCertificate_original_region chi hc (valuesTwentyFour (-1) (1) (-1))
      (twentyfour_table chi (by simpa using h5) (by simpa using h7) (by simpa using h13))
      (by decide) (by decide) twentyfour_certificate2 hx hb
  · exact rationalCertificate_original_region chi hc (valuesTwentyFour (-1) (1) (1))
      (twentyfour_table chi (by simpa using h5) (by simpa using h7) (by simpa using h13))
      (by decide) (by decide) twentyfour_certificate3 hx hb
  · exact rationalCertificate_original_region chi hc (valuesTwentyFour (1) (-1) (-1))
      (twentyfour_table chi (by simpa using h5) (by simpa using h7) (by simpa using h13))
      (by decide) (by decide) twentyfour_certificate4 hx hb
  · exact rationalCertificate_original_region chi hc (valuesTwentyFour (1) (-1) (1))
      (twentyfour_table chi (by simpa using h5) (by simpa using h7) (by simpa using h13))
      (by decide) (by decide) twentyfour_certificate5 hx hb
  · exact rationalCertificate_original_region chi hc (valuesTwentyFour (1) (1) (-1))
      (twentyfour_table chi (by simpa using h5) (by simpa using h7) (by simpa using h13))
      (by decide) (by decide) twentyfour_certificate6 hx hb
  · exact rationalCertificate_original_region chi hc (valuesTwentyFour (1) (1) (1))
      (twentyfour_table chi (by simpa using h5) (by simpa using h7) (by simpa using h13))
      (by decide) (by decide) twentyfour_certificate7 hx hb

end LiuWang.Proof.SmallConductorExpansion
