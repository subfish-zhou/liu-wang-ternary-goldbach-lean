import LiuWang.Proof.SmallConductorExclusion.Prefix
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# All nonprincipal characters modulo three and four

These are universal character statements, not a list of candidate conductors.
The nonprincipal character modulo four is also exhibited explicitly.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExclusion

theorem periodPrefix_three (chi : DirichletCharacter ℂ 3) (hc : chi ≠ 1) :
    PeriodPrefixNonnegative chi := by
  have hz : chi 0 = 0 := by
    simpa only [Nat.cast_zero] using
      DirichletLConditionalValueSeries.character_nat_zero_of_ne_one chi hc
  intro n hn
  interval_cases n <;> simp [characterPrefix, sum_range_succ, hz]

theorem periodPrefix_four (chi : DirichletCharacter ℂ 4) (hc : chi ≠ 1) :
    PeriodPrefixNonnegative chi := by
  have hz : chi 0 = 0 := by
    simpa only [Nat.cast_zero] using
      DirichletLConditionalValueSeries.character_nat_zero_of_ne_one chi hc
  have htwo : chi 2 = 0 := MulChar.map_nonunit chi (by decide : ¬IsUnit (2 : ZMod 4))
  intro n hn
  interval_cases n <;> simp [characterPrefix, sum_range_succ, hz, htwo]

theorem LFunction_three_ne_zero (chi : DirichletCharacter ℂ 3) (hc : chi ≠ 1)
    {sigma : ℝ} (hs : 0 < sigma) : chi.LFunction (sigma : ℂ) ≠ 0 :=
  LFunction_ne_zero_of_periodPrefix chi hc (periodPrefix_three chi hc) hs

theorem LFunction_four_ne_zero (chi : DirichletCharacter ℂ 4) (hc : chi ≠ 1)
    {sigma : ℝ} (hs : 0 < sigma) : chi.LFunction (sigma : ℂ) ≠ 0 :=
  LFunction_ne_zero_of_periodPrefix chi hc (periodPrefix_four chi hc) hs

def chiFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem chiFour_ne_one : chiFour ≠ 1 := by
  have hv : chiFour (3 : ZMod 4) = -1 := by
    change ((-1 : ℤ) : ℂ) = -1
    norm_num
  intro h
  have he := congrArg (fun chi : DirichletCharacter ℂ 4 => chi 3) h
  rw [hv, MulChar.one_apply (by decide : IsUnit (3 : ZMod 4))] at he
  norm_num at he

theorem chiFour_square : chiFour ^ 2 = 1 :=
  (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem chiFour_LFunction_re_lower {sigma : ℝ} (hs : 0 < sigma) :
    1 - (2 : ℝ) ^ (-sigma) ≤ (chiFour.LFunction (sigma : ℂ)).re :=
  LFunction_re_lower_of_periodPrefix chiFour chiFour_ne_one
    (periodPrefix_four chiFour chiFour_ne_one) hs

end LiuWang.Proof.SmallConductorExclusion
