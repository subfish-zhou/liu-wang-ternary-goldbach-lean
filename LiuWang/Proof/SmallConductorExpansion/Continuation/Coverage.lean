import LiuWang.Proof.SmallConductorExpansion.Main
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q33
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q34
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q35
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q36
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q37
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q38
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q39
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q40
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime43
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime67
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163

/-! # Exhaustive paid levels, rather than selected character instances -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def PaidLevel (q : ℕ) : Prop := q ≤ 40 ∨ q = 43 ∨ q = 67 ∨ q = 163

theorem quadratic_level_le_forty_original_region {q : ℕ} [NeZero q]
    (hq : q ≤ 40) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  by_cases hsmall : q ≤ 32
  · exact quadratic_level_le_thirtytwo_original_region hsmall chi hc hsq hx hb
  have he : q = 33 ∨ q = 34 ∨ q = 35 ∨ q = 36 ∨
      q = 37 ∨ q = 38 ∨ q = 39 ∨ q = 40 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact quadratic_33_original_region chi hc hsq hqx hb
  · exact quadratic_34_original_region chi hc hsq hqx hb
  · exact quadratic_35_original_region chi hc hsq hqx hb
  · exact quadratic_36_original_region chi hc hsq hqx hb
  · exact quadratic_37_original_region chi hc hsq hqx hb
  · exact quadratic_38_original_region chi hc hsq hqx hb
  · exact quadratic_39_original_region chi hc hsq hqx hb
  · exact quadratic_40_original_region chi hc hsq hqx hb

theorem paid_level_original_region {q : ℕ} [NeZero q]
    (hq : PaidLevel q) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rcases hq with hq | rfl | rfl | rfl
  · exact quadratic_level_le_forty_original_region hq chi hc hsq hx hqx hb
  · exact quadratic_43_original_region chi hc hsq hqx hb
  · exact quadratic_67_original_region chi hc hsq hqx hb
  · exact quadratic_163_original_region chi hc hsq hqx hb

end LiuWang.Proof.SmallConductorExpansion.Continuation
