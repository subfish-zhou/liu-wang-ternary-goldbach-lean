import LiuWang.Proof.SmallConductorExpansion.SmallPrimes
import LiuWang.Proof.SmallConductorExpansion.Eight
import LiuWang.Proof.SmallConductorExpansion.TwentyFour
import LiuWang.Proof.SmallConductorExpansion.Composites.Q6
import LiuWang.Proof.SmallConductorExpansion.Composites.Q9
import LiuWang.Proof.SmallConductorExpansion.Composites.Q10
import LiuWang.Proof.SmallConductorExpansion.Composites.Q12
import LiuWang.Proof.SmallConductorExpansion.Composites.Q14
import LiuWang.Proof.SmallConductorExpansion.Composites.Q15
import LiuWang.Proof.SmallConductorExpansion.Composites.Q16
import LiuWang.Proof.SmallConductorExpansion.Composites.Q18
import LiuWang.Proof.SmallConductorExpansion.Composites.Q20
import LiuWang.Proof.SmallConductorExpansion.Composites.Q21
import LiuWang.Proof.SmallConductorExpansion.Composites.Q22
import LiuWang.Proof.SmallConductorExpansion.Composites.Q25
import LiuWang.Proof.SmallConductorExpansion.Composites.Q26
import LiuWang.Proof.SmallConductorExpansion.Composites.Q27
import LiuWang.Proof.SmallConductorExpansion.Composites.Q28
import LiuWang.Proof.SmallConductorExpansion.Composites.Q30
import LiuWang.Proof.SmallConductorExpansion.Composites.Q32

/-!
# Every nonprincipal quadratic character at every level at most 32

The final finite split invokes character classification and paid certificates
at each level. In particular it is not a split of conductor integers with a
missing universal quantifier over their characters.
-/

set_option autoImplicit false
noncomputable section

open Complex

namespace LiuWang.Proof.SmallConductorExpansion

theorem quadratic_level_le_thirtytwo_original_region {q : ℕ} [NeZero q]
    (hq : q ≤ 32) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have hq3 : 3 ≤ q :=
    (BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hc).trans
      (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)
  have hb0 : 0 < beta := by linarith [original_region_ge_nineteen_twentieths hx hb]
  interval_cases q
  · exact LiuWang.Proof.SmallConductorExclusion.LFunction_three_ne_zero chi hc hb0
  · exact LiuWang.Proof.SmallConductorExclusion.LFunction_four_ne_zero chi hc hb0
  · exact quadratic_five_original_region chi hc hsq hx hb
  · exact q6_original_region chi hc hsq hx hb
  · exact smallPrime_original_region 7 (by decide) chi hc hsq hx hb
  · exact quadratic_eight_original_region chi hc hsq hx hb
  · exact q9_original_region chi hc hsq hx hb
  · exact q10_original_region chi hc hsq hx hb
  · exact smallPrime_original_region 11 (by decide) chi hc hsq hx hb
  · exact q12_original_region chi hc hsq hx hb
  · exact smallPrime_original_region 13 (by decide) chi hc hsq hx hb
  · exact q14_original_region chi hc hsq hx hb
  · exact q15_original_region chi hc hsq hx hb
  · exact q16_original_region chi hc hsq hx hb
  · exact smallPrime_original_region 17 (by decide) chi hc hsq hx hb
  · exact q18_original_region chi hc hsq hx hb
  · exact smallPrime_original_region 19 (by decide) chi hc hsq hx hb
  · exact q20_original_region chi hc hsq hx hb
  · exact q21_original_region chi hc hsq hx hb
  · exact q22_original_region chi hc hsq hx hb
  · exact smallPrime_original_region 23 (by decide) chi hc hsq hx hb
  · exact quadratic_twentyfour_original_region chi hc hsq hx hb
  · exact q25_original_region chi hc hsq hx hb
  · exact q26_original_region chi hc hsq hx hb
  · exact q27_original_region chi hc hsq hx hb
  · exact q28_original_region chi hc hsq hx hb
  · exact smallPrime_original_region 29 (by decide) chi hc hsq hx hb
  · exact q30_original_region chi hc hsq hx hb
  · exact smallPrime_original_region 31 (by decide) chi hc hsq hx hb
  · exact q32_original_region chi hc hsq hx hb

end LiuWang.Proof.SmallConductorExpansion
