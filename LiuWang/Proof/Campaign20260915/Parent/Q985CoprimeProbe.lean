import LiuWang.Proof.Campaign20260915.SmallConductors.Blocked.Q985.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace LiuWang.Proof.Campaign20260915.Parent.Q985CoprimeProbe

open SmallConductors.Blocked SmallConductors.Blocked.Q985
open SmallConductorExpansion.Continuation

private def fastEntry (n : ℕ) (w : Option (ℕ × ℕ)) : Prop :=
  match w with
  | none => ¬n.Coprime 985
  | some (s, mask) => s.Coprime 985 ∧
      (n : ZMod 985) = (s : ZMod 985) ^ 2 * squareWord 985 generators mask

private instance (n : ℕ) (w : Option (ℕ × ℕ)) : Decidable (fastEntry n w) := by
  unfold fastEntry
  cases w <;> infer_instance

/-- Same entries, with units decided by Euclid's algorithm rather than unit search. -/
theorem cover00 : ∀ i : Fin 32, 0 + i.val < 985 →
    Entry 985 generators (0 + i.val) (words.getD (0 + i.val) none) := by
  have h : ∀ i : Fin 32, 0 + i.val < 985 →
      fastEntry (0 + i.val) (words.getD (0 + i.val) none) := by
    decide +kernel
  intro i hi
  cases hw : words.getD (0 + i.val) none with
  | none => simpa only [hw, Entry, fastEntry, ZMod.isUnit_iff_coprime] using h i hi
  | some w =>
    rcases w with ⟨s, mask⟩
    simpa only [hw, Entry, fastEntry, ZMod.isUnit_iff_coprime] using h i hi

theorem cover_all : SquareWordCover 985 generators words := by
  have h : ∀ i : Fin 985, fastEntry i.val (words.getD i.val none) := by
    decide +kernel
  apply cover_of_entries
  intro n hn
  have hh := h ⟨n, hn⟩
  cases hw : words.getD n none with
  | none => simpa only [hw, Entry, fastEntry, ZMod.isUnit_iff_coprime] using hh
  | some w =>
    rcases w with ⟨s, mask⟩
    simpa only [hw, Entry, fastEntry, ZMod.isUnit_iff_coprime] using hh

#print axioms cover00
#print axioms cover_all

end LiuWang.Proof.Campaign20260915.Parent.Q985CoprimeProbe
