import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover

set_option autoImplicit false

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

def EntriesFrom {d : ℕ} (q : ℕ) (gs : Fin d → ℕ) (start : ℕ) :
    List (Option (ℕ × ℕ)) → Prop
  | [] => True
  | w :: ws => FastEntry q gs start w ∧ EntriesFrom q gs (start + 1) ws

instance {q d : ℕ} [NeZero q] (gs : Fin d → ℕ) (start : ℕ)
    (words : List (Option (ℕ × ℕ))) : Decidable (EntriesFrom q gs start words) := by
  induction words generalizing start with
  | nil => exact isTrue True.intro
  | cons w ws ih =>
    let : Decidable (EntriesFrom q gs (start + 1) ws) := ih _
    unfold EntriesFrom
    infer_instance

theorem entriesFrom_getD {q d : ℕ} {gs : Fin d → ℕ} {start : ℕ}
    {words : List (Option (ℕ × ℕ))} (h : EntriesFrom q gs start words) :
    ∀ i < words.length, FastEntry q gs (start + i) (words.getD i none) := by
  induction words generalizing start with
  | nil => simp
  | cons w ws ih =>
    intro i hi
    cases i with
    | zero => simpa using h.1
    | succ i =>
      simpa [List.getD_eq_getElem?_getD, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        ih h.2 i (by simpa using hi)

theorem cover_of_entries {q d : ℕ} [NeZero q] (gs : Fin d → ℕ)
    (words : List (Option (ℕ × ℕ))) (hlen : words.length = q)
    (h : EntriesFrom q gs 0 words) : SquareWordCover q gs words := by
  apply cover_of_fast_entries
  intro i
  simpa using entriesFrom_getD h i.val (by simpa only [hlen] using i.isLt)

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
