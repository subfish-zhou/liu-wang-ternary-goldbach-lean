import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Bounds

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

def blockSum (f : ℕ → ℝ) (start len : ℕ) : ℝ :=
  ∑ j ∈ Finset.range len, f (start + j)

theorem blockSum_one (f : ℕ → ℝ) (start : ℕ) :
    blockSum f start 1 = f start := by simp [blockSum]

theorem blockSum_add (f : ℕ → ℝ) (start m n : ℕ) :
    blockSum f start (m + n) = blockSum f start m + blockSum f (start + m) n := by
  simp only [blockSum, Finset.sum_range_add, Nat.add_assoc]

theorem block_upper {f : ℕ → ℝ} {start m n : ℕ} {a b c : ℝ}
    (ha : blockSum f start m ≤ a) (hb : blockSum f (start + m) n ≤ b)
    (hc : a + b ≤ c) : blockSum f start (m + n) ≤ c := by
  rw [blockSum_add]
  exact (add_le_add ha hb).trans hc

theorem block_lower {f : ℕ → ℝ} {start m n : ℕ} {a b c : ℝ}
    (ha : a ≤ blockSum f start m) (hb : b ≤ blockSum f (start + m) n)
    (hc : c ≤ a + b) : c ≤ blockSum f start (m + n) := by
  rw [blockSum_add]
  exact hc.trans (add_le_add ha hb)

def rowCell (row k : ℕ) : ℝ :=
  match row with
  | 0 => cellUpper 1116 (gridPoint k) (gridPoint (k + 1))
  | 1 => cellUpper 1209 (gridPoint k) (gridPoint (k + 1))
  | 2 => cellUpper 1302 (gridPoint k) (gridPoint (k + 1))
  | 3 => cellUpper 1395 (gridPoint k) (gridPoint (k + 1))
  | 4 => cellUpper 1426 (gridPoint k) (gridPoint (k + 1))
  | 5 => cellUpper 1457 (gridPoint k) (gridPoint (k + 1))
  | 6 => cellUpper (2945 / 2) (gridPoint k) (gridPoint (k + 1))
  | _ => cellLower (7409 / 5) (gridPoint k) (gridPoint (k + 1))

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
