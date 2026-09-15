import LiuWang.Proof.SmallConductorExpansion.Continuation.Weighted

/-! # One shared accumulator, testing the old prefixes 0,...,q-1 -/

set_option autoImplicit false

open Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def scan (v : ℕ → ℤ) (P : ℚ) : ℕ → ℤ × Bool
  | 0 => (0, true)
  | n + 1 =>
      let s := scan v P n
      (s.1 + v n, s.2 && decide (|(s.1 : ℚ)| ≤ P))

theorem scan_acc (v : ℕ → ℤ) (P : ℚ) (n : ℕ) :
    (scan v P n).1 = ∑ k ∈ range n, v k := by
  induction n with
  | zero => simp [scan]
  | succ n ih => simp [scan, ih, Finset.sum_range_succ]

theorem scan_ok (v : ℕ → ℤ) (P : ℚ) (n : ℕ) :
    (scan v P n).2 = true ↔
      ∀ i ∈ range n, |((∑ k ∈ range i, v k : ℤ) : ℚ)| ≤ P := by
  induction n with
  | zero => simp [scan]
  | succ n ih =>
      simp only [scan, Bool.and_eq_true, decide_eq_true_eq, ih, scan_acc]
      rw [Finset.range_add_one, Finset.forall_mem_insert]
      exact and_comm

def prefixCheck (q : ℕ) (values : List ℤ) (P : ℚ) : Bool :=
  (scan (tableValue q values) P q).2

def periodSum (q : ℕ) (values : List ℤ) : ℤ :=
  (scan (tableValue q values) 0 q).1

theorem prefixCheck_iff (q : ℕ) (values : List ℤ) (P : ℚ) :
    prefixCheck q values P = true ↔
      ∀ i ∈ range q, |((∑ k ∈ range i, tableValue q values k : ℤ) : ℚ)| ≤ P :=
  scan_ok _ _ _

theorem periodSum_eq (q : ℕ) (values : List ℤ) :
    periodSum q values = ∑ k ∈ range q, tableValue q values k :=
  scan_acc _ _ _

def Signed (q : ℕ) (values : List ℤ) (m : ℕ) (P C : ℚ) : Prop :=
  prefixCheck q values P = true ∧
    C * (∑ k ∈ range m, (max (-(tableValue q values k)) 0 : ℚ) / k) +
      2 * P * C / m < ∑ k ∈ range m, (max (tableValue q values k) 0 : ℚ) / k

def Aligned (q : ℕ) (values : List ℤ) (m : ℕ) (P C : ℚ) : Prop :=
  prefixCheck q values P = true ∧
    C * (∑ k ∈ range m, (max (-(tableValue q values k)) 0 : ℚ) / k) +
      P * C / m < ∑ k ∈ range m, (max (tableValue q values k) 0 : ℚ) / k

def Weighted (q : ℕ) (values : List ℤ) (m : ℕ) (P A : ℚ) : Prop :=
  prefixCheck q values P = true ∧
    (∑ k ∈ range m, dyadicEnvelope A k * (max (-(tableValue q values k)) 0 : ℚ) / k) +
      P * dyadicEnvelope A m / m <
      ∑ k ∈ range m, (max (tableValue q values k) 0 : ℚ) / k

theorem signed_iff (q : ℕ) (values : List ℤ) (m : ℕ) (P C : ℚ) :
    Signed q values m P C ↔ RationalCertificate q values m P C :=
  and_congr (prefixCheck_iff q values P) Iff.rfl

theorem aligned_iff (q : ℕ) (values : List ℤ) (m : ℕ) (P C : ℚ) :
    Aligned q values m P C ↔ RationalAlignedCertificate q values m P C :=
  and_congr (prefixCheck_iff q values P) Iff.rfl

theorem weighted_iff (q : ℕ) (values : List ℤ) (m : ℕ) (P A : ℚ) :
    Weighted q values m P A ↔ RationalWeightedCertificate q values m P A :=
  and_congr (prefixCheck_iff q values P) Iff.rfl

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
