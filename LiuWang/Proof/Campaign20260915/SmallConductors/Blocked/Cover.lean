import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Blocked

def Entry {d : ℕ} (q : ℕ) (gs : Fin d → ℕ) (n : ℕ)
    (word : Option (ℕ × ℕ)) : Prop :=
  match word with
  | none => ¬IsUnit (n : ZMod q)
  | some (s, mask) =>
    IsUnit (s : ZMod q) ∧ (n : ZMod q) = (s : ZMod q) ^ 2 * squareWord q gs mask

instance {q d : ℕ} [NeZero q] (gs : Fin d → ℕ) (n : ℕ)
    (word : Option (ℕ × ℕ)) : Decidable (Entry q gs n word) := by
  unfold Entry
  cases word <;> infer_instance

theorem cover_of_entries {q d : ℕ} [NeZero q] (gs : Fin d → ℕ)
    (words : List (Option (ℕ × ℕ)))
    (h : ∀ n, n < q → Entry q gs n (words.getD n none)) :
    SquareWordCover q gs words := by
  intro z
  have hz := h z.val z.val_lt
  cases he : words.getD z.val none with
  | none => simpa only [he, Entry, ZMod.natCast_zmod_val] using hz
  | some w =>
    rcases w with ⟨s, mask⟩
    simpa only [he, Entry, ZMod.natCast_zmod_val] using hz

theorem cover_of_blocks {q d blocks width : ℕ} [NeZero q]
    (gs : Fin d → ℕ) (words : List (Option (ℕ × ℕ)))
    (hw : 0 < width) (hq : q ≤ blocks * width)
    (h : ∀ b : Fin blocks, ∀ i : Fin width,
      width * b.val + i.val < q →
        Entry q gs (width * b.val + i.val)
          (words.getD (width * b.val + i.val) none)) :
    SquareWordCover q gs words := by
  apply cover_of_entries gs words
  intro n hn
  have hb : n / width < blocks := (Nat.div_lt_iff_lt_mul hw).mpr (hn.trans_le hq)
  have hi : n % width < width := Nat.mod_lt _ hw
  have he : width * (n / width) + n % width = n := by
    simpa only [Nat.add_comm] using Nat.mod_add_div n width
  simpa only [he] using h ⟨n / width, hb⟩ ⟨n % width, hi⟩ (by simpa only [he] using hn)

end LiuWang.Proof.Campaign20260915.SmallConductors.Blocked
