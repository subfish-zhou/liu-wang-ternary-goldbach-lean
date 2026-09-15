import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.IntegerBounds
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListScan
import Mathlib.Data.List.GetD

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.SmallConductorExpansion
open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

def sumList (f : ℕ → ℤ → ℤ) (start : ℕ) : List ℤ → ℤ
  | [] => 0
  | v :: vs => f start v + sumList f (start + 1) vs

theorem sumList_eq (f : ℕ → ℤ → ℤ) (start : ℕ) (values : List ℤ) :
    sumList f start values =
      ∑ k ∈ range values.length, f (start + k) (values.getD k 0) := by
  induction values generalizing start with
  | nil => simp [sumList]
  | cons v vs ih =>
    simp [sumList, ih, sum_range_succ', List.getD_eq_getElem?_getD,
      Nat.add_left_comm, add_comm]

def repeatValues (values : List ℤ) : ℕ → List ℤ
  | 0 => []
  | t + 1 => values ++ repeatValues values t

theorem repeatValues_length (values : List ℤ) (t : ℕ) :
    (repeatValues values t).length = t * values.length := by
  induction t with
  | zero => simp [repeatValues]
  | succ t ih => simp [repeatValues, ih, Nat.succ_mul, Nat.add_comm]

theorem repeatValues_getD (values : List ℤ) (t k : ℕ)
    (hk : k < t * values.length) :
    (repeatValues values t).getD k 0 = values.getD (k % values.length) 0 := by
  induction t generalizing k with
  | zero => simp at hk
  | succ t ih =>
    rw [repeatValues]
    by_cases h : k < values.length
    · rw [List.getD_append _ _ _ _ h, Nat.mod_eq_of_lt h]
    · have hle : values.length ≤ k := by omega
      rw [List.getD_append_right _ _ _ _ hle, ih]
      · rw [← Nat.mod_eq_sub_mod hle]
      · rw [Nat.succ_mul] at hk
        omega

def ListRounded (q t : ℕ) (values : List ℤ) (P A B : ℚ) : Prop :=
  sumList (fun k v => ⌈B * (dyadicEnvelope A k * (max (-v) 0 : ℚ) / k)⌉)
      0 (repeatValues values t) +
    ⌈B * (P * dyadicEnvelope A (t * q) / (t * q))⌉ <
  sumList (fun k v => ⌊B * ((max v 0 : ℚ) / k)⌋) 0 (repeatValues values t)

instance (q t : ℕ) (values : List ℤ) (P A B : ℚ) :
    Decidable (ListRounded q t values P A B) := by
  unfold ListRounded
  infer_instance

theorem rounded_of_list {q t : ℕ} {values : List ℤ} {P A B : ℚ}
    (hlen : values.length = q) (h : ListRounded q t values P A B) :
    Rounded q values (t * q) P A B := by
  unfold ListRounded at h
  simp only [sumList_eq, repeatValues_length, hlen, zero_add] at h
  have he : ∀ k ∈ range (t * q),
      (repeatValues values t).getD k 0 = tableValue q values k := by
    intro k hk
    simpa only [tableValue, hlen] using
      repeatValues_getD values t k (by simpa only [hlen] using mem_range.mp hk)
  have hu := sum_congr rfl (fun (k : ℕ) hk => congrArg
    (fun v : ℤ => ⌈B * (dyadicEnvelope A k * (max (-v) 0 : ℚ) / k)⌉) (he k hk))
  have hl := sum_congr rfl (fun (k : ℕ) hk => congrArg
    (fun v : ℤ => ⌊B * ((max v 0 : ℚ) / k)⌋) (he k hk))
  rw [hu, hl] at h
  simpa only [Rounded, Nat.cast_mul] using h

theorem weighted_of_list {q t : ℕ} {values : List ℤ} {P A B : ℚ}
    (hlen : values.length = q) (hp : prefixList P 0 values = true) (hB : 0 < B)
    (h : ListRounded q t values P A B) :
    VerifiedScan.Weighted q values (t * q) P A :=
  weighted_of_rounded (prefixCheck_of_prefixList hlen hp) hB (rounded_of_list hlen h)

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
