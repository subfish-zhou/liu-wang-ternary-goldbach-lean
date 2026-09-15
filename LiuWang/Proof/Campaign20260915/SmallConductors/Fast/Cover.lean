import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

def FastEntry {d : ℕ} (q : ℕ) (gs : Fin d → ℕ) (n : ℕ)
    (word : Option (ℕ × ℕ)) : Prop :=
  match word with
  | none => ¬n.Coprime q
  | some (s, mask) =>
    s.Coprime q ∧ (n : ZMod q) = (s : ZMod q) ^ 2 * squareWord q gs mask

instance {q d : ℕ} [NeZero q] (gs : Fin d → ℕ) (n : ℕ)
    (word : Option (ℕ × ℕ)) : Decidable (FastEntry q gs n word) := by
  unfold FastEntry
  cases word <;> infer_instance

theorem cover_of_fast_entries {q d : ℕ} [NeZero q] (gs : Fin d → ℕ)
    (words : List (Option (ℕ × ℕ)))
    (h : ∀ i : Fin q, FastEntry q gs i.val (words.getD i.val none)) :
    SquareWordCover q gs words := by
  intro z
  have hz := h ⟨z.val, z.val_lt⟩
  cases he : words.getD z.val none with
  | none =>
    simpa only [he, FastEntry, ← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val] using hz
  | some w =>
    rcases w with ⟨s, mask⟩
    simpa only [he, FastEntry, ← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val] using hz

theorem generators_unit_of_coprime {q d : ℕ} (gs : Fin d → ℕ)
    (h : ∀ i, (gs i).Coprime q) : ∀ i, IsUnit (gs i : ZMod q) :=
  fun i => (ZMod.isUnit_iff_coprime (gs i) q).mpr (h i)

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
