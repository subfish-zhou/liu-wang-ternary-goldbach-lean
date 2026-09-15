import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.FourPhases
import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralTripleSelection
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.ClosedCounts

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

instance conductorNeZero {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩

theorem level_one_LFunction {d : ℕ} [NeZero d] (hd : d = 1) (chi : DirichletCharacter ℂ d) :
    chi.LFunction = riemannZeta := by
  subst d
  rw [Subsingleton.elim chi 1, DirichletCharacter.LFunction_modOne_eq]

theorem canonical_order {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderNatAt chi.LFunction z = analyticOrderNatAt chi.primitiveCharacter.LFunction z := by
  by_cases hc : chi = 1
  · subst chi
    have hd : (1 : DirichletCharacter ℂ q).conductor = 1 := DirichletCharacter.conductor_one
    have hv := level_one_LFunction hd (1 : DirichletCharacter ℂ q).primitiveCharacter
    rw [hv]
    exact PrincipalPsi.analyticOrderNatAt_principal_eq_zeta h0
      (by intro he; simp [he] at h1)
  · exact BombieriVinogradov.SiegelWalfisz.analyticOrderNatAt_LFunction_eq_primitive chi hc h0

theorem common_lift_order {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hd : d ∣ q) (he : e ∣ q) (h : chi.changeLevel hd = psi.changeLevel he)
    {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderNatAt chi.LFunction z = analyticOrderNatAt psi.LFunction z := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let : NeZero psi.conductor := ⟨psi.conductor_ne_zero⟩
  have hh : chi.changeLevel hd =
      psi.primitiveCharacter.changeLevel (psi.conductor_dvd_level.trans he) := by
    rw [DirichletCharacter.changeLevel_trans psi.primitiveCharacter psi.conductor_dvd_level he,
      DirichletCharacter.changeLevel_primitiveCharacter]
    exact h
  have hf : chi.primitiveCharacter.LFunction = psi.primitiveCharacter.LFunction :=
    funext (common_lift_primitive_LFunction chi psi.primitiveCharacter hd
      (psi.conductor_dvd_level.trans he) psi.primitiveCharacter_isPrimitive hh)
  rw [canonical_order chi h0 h1, canonical_order psi h0 h1, hf]

theorem primitive_label_unique {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hd : d ∣ q) (he : e ∣ q) (hc : chi.IsPrimitive) (hp : psi.IsPrimitive)
    (h : chi.changeLevel hd = psi.changeLevel he) :
    d = e ∧ ∀ n : ℕ, chi n = psi n := by
  have hde : d = e := by
    have hh := congrArg DirichletCharacter.conductor h
    rwa [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
      hc, hp] at hh
  refine ⟨hde, ?_⟩
  subst e
  have hh := DirichletCharacter.changeLevel_injective hd h
  intro n
  rw [hh]

def primitiveSlot {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q alpha y) : ZeroSlots p.character.conductor alpha y :=
  let : NeZero p.character.conductor := ⟨p.character.conductor_ne_zero⟩
  {
    character := p.character.primitiveCharacter
    value := p.value
    index := p.index
    zero_mem := by
      have hz := mem_strictZeroValues.mp p.zero_mem
      have hi := p.index_lt
      rw [canonical_order p.character hz.2.1 hz.2.2.2.1] at hi
      exact mem_strictZeroValues.mpr
        ⟨apply_eq_zero_of_analyticOrderNatAt_ne_zero (by omega), hz.2⟩
    index_lt := by
      rw [← canonical_order p.character (mem_strictZeroValues.mp p.zero_mem).2.1
        (mem_strictZeroValues.mp p.zero_mem).2.2.2.1]
      exact p.index_lt
  }

theorem primitiveSlot_value {q : ℕ} [NeZero q] {alpha y : ℝ} (p : ZeroSlots q alpha y) :
    (primitiveSlot p).value = p.value := rfl

theorem primitiveSlot_index {q : ℕ} [NeZero q] {alpha y : ℝ} (p : ZeroSlots q alpha y) :
    (primitiveSlot p).index = p.index := rfl

theorem primitiveSlot_reconstruct {q : ℕ} [NeZero q] {alpha y : ℝ} (p : ZeroSlots q alpha y) :
    (primitiveSlot p).character.changeLevel p.character.conductor_dvd_level = p.character :=
  p.character.changeLevel_primitiveCharacter

theorem same_canonical_data_same_slot {q : ℕ} [NeZero q] {alpha y : ℝ}
    {p r : ZeroSlots q alpha y}
    (hc : p.character.primitiveCharacter.changeLevel p.character.conductor_dvd_level =
      r.character.primitiveCharacter.changeLevel r.character.conductor_dvd_level)
    (hv : p.value = r.value) (hi : p.index = r.index) : p = r := by
  rw [DirichletCharacter.changeLevel_primitiveCharacter,
    DirichletCharacter.changeLevel_primitiveCharacter] at hc
  exact zeroSlots_ext hc hv hi

theorem primitive_principal_iff {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    chi.primitiveCharacter = 1 ↔ chi = 1 := by
  rw [← DirichletCharacter.changeLevel_eq_one_iff chi.conductor_dvd_level,
    DirichletCharacter.changeLevel_primitiveCharacter]

theorem primitive_principal_level {d : ℕ} [NeZero d]
    (chi : DirichletCharacter ℂ d) (hp : chi.IsPrimitive) (hc : chi = 1) : d = 1 := by
  rw [hc, DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hp
  exact hp.symm

theorem canonical_conjugate_values {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    (chi⁻¹).conductor = chi.conductor ∧
      ∀ n : ℕ, (chi⁻¹).primitiveCharacter n = (chi.primitiveCharacter⁻¹) n := by
  have hp : (chi.primitiveCharacter⁻¹).IsPrimitive := by
    simpa only [lwdSignedCharacter, if_true] using
      lwd_signed_primitive chi.primitiveCharacter chi.primitiveCharacter_isPrimitive true
  apply primitive_label_unique (chi⁻¹).primitiveCharacter chi.primitiveCharacter⁻¹
    (chi⁻¹).conductor_dvd_level chi.conductor_dvd_level (chi⁻¹).primitiveCharacter_isPrimitive hp
  rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter,
    DirichletCharacter.changeLevel_primitiveCharacter]

theorem canonical_level_bounds {q : ℕ} [NeZero q] {x alpha y : ℝ}
    (hq : (q : ℝ) ≤ x) (p : ZeroSlots q alpha y) :
    0 < p.character.conductor ∧ p.character.conductor ∣ q ∧
      p.character.conductor ≤ q ∧ (p.character.conductor : ℝ) ≤ x := by
  have hd := Nat.le_of_dvd (NeZero.pos q) p.character.conductor_dvd_level
  exact ⟨NeZero.pos _, p.character.conductor_dvd_level, hd, (Nat.cast_le.mpr hd).trans hq⟩

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples
