import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Prefix

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.SmallConductorExpansion
open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

def prefixList (P : ℚ) (acc : ℤ) : List ℤ → Bool
  | [] => true
  | v :: vs => decide (|(acc : ℚ)| ≤ P) && prefixList P (acc + v) vs

theorem prefixList_bound {P : ℚ} {acc : ℤ} {values : List ℤ}
    (h : prefixList P acc values = true) :
    ∀ i < values.length, |((acc + ∑ k ∈ range i, values.getD k 0 : ℤ) : ℚ)| ≤ P := by
  induction values generalizing acc with
  | nil => simp
  | cons v vs ih =>
    simp only [prefixList, Bool.and_eq_true, decide_eq_true_eq] at h
    intro i hi
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hh := ih h.2 i (by simpa using hi)
      simpa [sum_range_succ', List.getD_eq_getElem?_getD, add_assoc,
        add_comm, add_left_comm] using hh

theorem sum_range_getD (values : List ℤ) :
    (∑ k ∈ range values.length, values.getD k 0) = values.sum := by
  induction values with
  | nil => simp
  | cons v vs ih =>
    simpa [sum_range_succ', List.getD_eq_getElem?_getD, add_comm] using
      congrArg (v + ·) ih

theorem table_sum_eq_getD {q i : ℕ} {values : List ℤ} (hi : i ≤ q) :
    (∑ k ∈ range i, tableValue q values k) = ∑ k ∈ range i, values.getD k 0 := by
  apply sum_congr rfl
  intro k hk
  simp only [tableValue, Nat.mod_eq_of_lt (lt_of_lt_of_le (mem_range.mp hk) hi)]

theorem prefixCheck_of_prefixList {q : ℕ} {values : List ℤ} {P : ℚ}
    (hlen : values.length = q) (h : prefixList P 0 values = true) :
    VerifiedScan.prefixCheck q values P = true := by
  rw [VerifiedScan.prefixCheck_iff]
  intro i hi
  have hiq := mem_range.mp hi
  have hh := prefixList_bound h i (by omega)
  rw [table_sum_eq_getD (Nat.le_of_lt hiq)]
  simpa using hh

theorem periodSum_eq_list_sum {q : ℕ} {values : List ℤ} (hlen : values.length = q) :
    VerifiedScan.periodSum q values = values.sum := by
  rw [VerifiedScan.periodSum_eq, table_sum_eq_getD le_rfl, ← hlen, sum_range_getD]

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
