import LiuWang.Proof.CharacterExpansion.GaussInduction

/-!
# Liu--Wang finite character-expansion contract

Equations (3.13)--(3.15) and (4.9), with an explicit conjugate Gauss convention.
Both principal and nonprincipal characters occur in the full finite family.
The modulus-one endpoint has zero error and requires no exceptional case in
the general theorems.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.CharacterExpansion

open LiuWang.Proof.Interfaces
open AnalyticNumberTheory.LargeSieve
open scoped BigOperators

theorem character_level_one_apply (χ : Character 1) (x : ZMod 1) : χ x = 1 := by
  rw [Subsingleton.elim x 1, map_one]

@[simp] theorem G_one (a : Nat) (χ : Character 1) : G a χ = 1 := by
  have he (x : ZMod 1) : ZMod.stdAddChar x = 1 := by
    rw [Subsingleton.elim x 0, AddChar.map_zero_eq_one]
  simp [G, gaussSum, character_level_one_apply, AddChar.mulShift_apply, he]

@[simp] theorem twistedS_one (N : Nat) (η : Real) (χ : Character 1) :
    twistedS N η χ = S N η := by
  simp [twistedS, S, LiuWang.Fourier.liuWangExpSum, LiuWang.Fourier.indexedExpSum,
    character_level_one_apply, windowFinset]

theorem S_character_expansion_one (N : Nat) (η : Real) :
    S N (1 + η) = S N η ∧ nonCoprimeError N 1 (1 + η) = 0 := by
  refine ⟨?_, nonCoprimeError_one N _⟩
  simpa [rationalCenter] using S_character_expansion (q := 1) N 1 η

theorem source_contract {N a q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hi : sourceIndex a q)
    (hqP : (q : Real) ≤ sourceP1 N) (η : Real) :
    S N (rationalCenter a q + η) =
      (q.totient : Complex)⁻¹ *
        (∑ χ : Character q, G a χ * twistedS N η χ) +
      nonCoprimeError N q (rationalCenter a q + η) ∧
    ‖nonCoprimeError N q (rationalCenter a q + η)‖ ≤
      sourceL N ^ 2 / Real.log 2 ∧
    ∀ χ : Character q, ‖G a χ‖ ≤ Real.sqrt χ.conductor := by
  exact ⟨S_character_expansion N a η,
    norm_nonCoprimeError_le_source hN (hi.1.trans hi.2.1) hqP _,
    fun χ => norm_G_le_sqrt_conductor hi.2.2 χ⟩

end LiuWang.Proof.CharacterExpansion
