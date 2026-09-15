import LiuWang.Proof.SmallConductorExpansion.Continuation.Consumer
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q41
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q42
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q44
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q45
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q46
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q47
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q48
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q49
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q50
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q51
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q52
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q53
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q54
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q55
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q56
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q57
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q58
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q59
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q60
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q61
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q62
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q63
import LiuWang.Proof.SmallConductorExpansion.Continuation.Q64

/-! # The next paid prefix: all quadratic characters through level 64 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def PaidLevel64 (q : ℕ) : Prop := q ≤ 64 ∨ q = 67 ∨ q = 163

theorem quadratic_level_le_sixtyfour_original_region {q : ℕ} [NeZero q]
    (hq : q ≤ 64) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  by_cases hsmall : q ≤ 40
  · exact quadratic_level_le_forty_original_region hsmall chi hc hsq hx hqx hb
  have he : q = 41 ∨ q = 42 ∨ q = 43 ∨ q = 44 ∨ q = 45 ∨ q = 46 ∨ q = 47 ∨ q = 48 ∨ q = 49 ∨ q = 50 ∨ q = 51 ∨ q = 52 ∨ q = 53 ∨ q = 54 ∨ q = 55 ∨ q = 56 ∨ q = 57 ∨ q = 58 ∨ q = 59 ∨ q = 60 ∨ q = 61 ∨ q = 62 ∨ q = 63 ∨ q = 64 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact quadratic_41_original_region chi hc hsq hqx hb
  · exact quadratic_42_original_region chi hc hsq hqx hb
  · exact quadratic_43_original_region chi hc hsq hqx hb
  · exact quadratic_44_original_region chi hc hsq hqx hb
  · exact quadratic_45_original_region chi hc hsq hqx hb
  · exact quadratic_46_original_region chi hc hsq hqx hb
  · exact quadratic_47_original_region chi hc hsq hqx hb
  · exact quadratic_48_original_region chi hc hsq hqx hb
  · exact quadratic_49_original_region chi hc hsq hqx hb
  · exact quadratic_50_original_region chi hc hsq hqx hb
  · exact quadratic_51_original_region chi hc hsq hqx hb
  · exact quadratic_52_original_region chi hc hsq hqx hb
  · exact quadratic_53_original_region chi hc hsq hqx hb
  · exact quadratic_54_original_region chi hc hsq hqx hb
  · exact quadratic_55_original_region chi hc hsq hqx hb
  · exact quadratic_56_original_region chi hc hsq hqx hb
  · exact quadratic_57_original_region chi hc hsq hqx hb
  · exact quadratic_58_original_region chi hc hsq hqx hb
  · exact quadratic_59_original_region chi hc hsq hqx hb
  · exact quadratic_60_original_region chi hc hsq hqx hb
  · exact quadratic_61_original_region chi hc hsq hqx hb
  · exact quadratic_62_original_region chi hc hsq hqx hb
  · exact quadratic_63_original_region chi hc hsq hqx hb
  · exact quadratic_64_original_region chi hc hsq hqx hb

theorem paid_level64_original_region {q : ℕ} [NeZero q]
    (hq : PaidLevel64 q) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rcases hq with hq | rfl | rfl
  · exact quadratic_level_le_sixtyfour_original_region hq chi hc hsq hx hqx hb
  · exact quadratic_67_original_region chi hc hsq hqx hb
  · exact quadratic_163_original_region chi hc hsq hqx hb

theorem primitive_paid64_source_original_region (d : PrimitiveQuadraticDatum)
    (hd : PaidLevel64 d.modulus) {x beta : ℝ}
    (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    datumL d (beta : ℂ) ≠ 0 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  exact paid_level64_original_region hd d.character d.ne_one d.square_eq_one hx hdx hb

theorem original_real_zero_source_unpaid64 (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hz : datumL d (beta : ℂ) = 0) :
    65 ≤ d.modulus ∧ d.modulus ≠ 67 ∧ d.modulus ≠ 163 := by
  have hn : ¬PaidLevel64 d.modulus := fun hd =>
    primitive_paid64_source_original_region d hd hx hdx hb hz
  unfold PaidLevel64 at hn
  omega

theorem family_twentyfour_conductor_unpaid64
    {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (rho : ℂ)
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho = 0) :
    ∃ d : PrimitiveQuadraticDatum,
      (65 ≤ d.modulus ∧ d.modulus ≠ 67 ∧ d.modulus ≠ 163) ∧
      (d.modulus : ℝ) ≤ x ∧ d.modulus = chi.conductor ∧ inducedAt d q = chi ∧
      datumL d rho = 0 ∧ rho.im = 0 ∧ analyticOrderNatAt chi.LFunction rho = 1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1 - 1 / (24 * Real.log x) < tau.re → |tau.im| ≤ x / (r : ℝ) →
          (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau = 0 →
            tau = rho ∧ d.modulus = psi.conductor ∧ d.modulus ∣ r ∧
              inducedAt d r = psi ∧ analyticOrderNatAt psi.LFunction tau = 1 := by
  obtain ⟨d, hd, hdc, hdi, hdz, hi, ho, hall⟩ :=
    RealClosure.family_twentyfour_from_actual_zero hx hq chi rho hr ht hp hz
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hbound := original_real_zero_source_unpaid64 d hx hd
    (r24_re_in_original_real_region hx hr) (by simpa only [he] using hdz)
  exact ⟨d, hbound, hd, hdc, hdi, hdz, hi, ho, hall⟩

theorem ordinary_paid64_conductor_ne_zero
    {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (hc : PaidLevel64 chi.conductor) {rho : ℂ}
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) : chi.LFunction rho ≠ 0 := by
  intro hz
  obtain ⟨d, hd, _, hdc, _⟩ :=
    family_twentyfour_conductor_unpaid64 hx hq chi rho hr ht hp hz
  rw [← hdc] at hc
  unfold PaidLevel64 at hc
  omega

end LiuWang.Proof.SmallConductorExpansion.Continuation
