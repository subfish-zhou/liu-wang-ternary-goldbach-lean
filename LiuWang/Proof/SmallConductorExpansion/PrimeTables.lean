import LiuWang.Proof.SmallConductorExpansion.Tables
import LiuWang.Proof.EffectiveLValue.EvenHelpers.IntegralQuotient.CoprimeParity

/-!
# Prime-conductor classification and finite character tables

At an odd prime there is exactly one nonprincipal quadratic character.
The existing cyclic-unit classification identifies every such actual character
with the complex embedding of the finite-field quadratic character.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def primeCharacter (p : ℕ) [Fact p.Prime] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem primeCharacter_square (p : ℕ) [Fact p.Prime] : primeCharacter p ^ 2 = 1 :=
  ((quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)).sq_eq_one

theorem primeCharacter_ne_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    primeCharacter p ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
    (quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n]))

theorem quadratic_prime_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (chi : DirichletCharacter ℂ p) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) :
    chi = primeCharacter p :=
  LiuWang.Proof.EffectiveLValue.quadratic_cyclic_eq chi (primeCharacter p)
    hsq (primeCharacter_square p) hc (primeCharacter_ne_one p hp)

theorem primeCharacter_isPrimitive (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (primeCharacter p).IsPrimitive := by
  have hd := (primeCharacter p).conductor_dvd_level
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h
  · exact False.elim ((primeCharacter_ne_one p hp)
      (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · exact h

theorem primeCharacter_table (p : ℕ) [Fact p.Prime]
    (values : List ℤ)
    (h : ∀ a : ZMod p, quadraticCharFun (ZMod p) a = values.getD a.val 0) :
    ∀ a : ZMod p, primeCharacter p a = (values.getD a.val 0 : ℂ) := by
  intro a
  change ((quadraticCharFun (ZMod p) a : ℤ) : ℂ) = _
  rw [h a]

def valuesFive : List ℤ := [0, 1, -1, -1, 1]

instance five_prime : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem primeCharacter_five_table :
    ∀ a : ZMod 5, primeCharacter 5 a = (valuesFive.getD a.val 0 : ℂ) :=
  primeCharacter_table 5 valuesFive (by decide)

theorem valuesFive_certificate : RationalCertificate 5 valuesFive 20 1 (6 / 5) := by
  constructor
  · decide
  · norm_num [tableValue, valuesFive, Finset.sum_range_succ]

theorem quadratic_five_original_region (chi : DirichletCharacter ℂ 5)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rw [quadratic_prime_eq 5 (by decide) chi hc hsq]
  exact rationalCertificate_original_region (primeCharacter 5)
    (primeCharacter_ne_one 5 (by decide)) valuesFive primeCharacter_five_table
    (by decide) (by decide) valuesFive_certificate hx hb

theorem primeCharacter_five_negative_prefix :
    LiuWang.Proof.SmallConductorExclusion.characterPrefix (primeCharacter 5) 4 = -1 := by
  unfold LiuWang.Proof.SmallConductorExclusion.characterPrefix
  norm_num [Finset.sum_range_succ, primeCharacter_five_table, valuesFive]

theorem primeCharacter_five_not_old_certificate :
    ¬LiuWang.Proof.SmallConductorExclusion.PeriodPrefixNonnegative (primeCharacter 5) := by
  intro h
  have hh := h 4 (by decide)
  rw [primeCharacter_five_negative_prefix] at hh
  norm_num at hh

end LiuWang.Proof.SmallConductorExpansion
