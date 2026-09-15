import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.SmallConductorExpansion
open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

def upperDiv (u z : ℤ) (k : ℕ) : ℤ := - (-(u * z) / (k : ℤ))

theorem upperDiv_eq (u z : ℤ) (k : ℕ) :
    upperDiv u z k = ⌈(u : ℚ) * z / k⌉ := by
  have hceil (a : ℚ) : ⌈a⌉ = -⌊-a⌋ := by simpa using (Int.ceil_neg (a := -a))
  rw [hceil, ← neg_div, Int.floor_div_natCast]
  have he : -((u : ℚ) * z) = ((-(u * z) : ℤ) : ℚ) := by push_cast; rfl
  rw [he, Int.floor_intCast]
  rfl

theorem lowerDiv_eq (u z : ℤ) (k : ℕ) :
    u * z / (k : ℤ) = ⌊(u : ℚ) * z / k⌋ := by
  rw [Int.floor_div_natCast, ← Int.cast_mul, Int.floor_intCast]

def IntegerRounded (q t : ℕ) (values upper : List ℤ) (P B : ℤ) : Prop :=
  sumList (fun k v => upperDiv (upper.getD (Nat.clog 2 k) 0) (max (-v) 0) k)
      0 (repeatValues values t) +
    upperDiv (upper.getD (Nat.clog 2 (t * q)) 0) P (t * q) <
  sumList (fun k v => B * max v 0 / (k : ℤ)) 0 (repeatValues values t)

instance (q t : ℕ) (values upper : List ℤ) (P B : ℤ) :
    Decidable (IntegerRounded q t values upper P B) := by
  unfold IntegerRounded
  infer_instance

theorem ceil_weight_le {a : ℚ} {B u z : ℤ} (h : (B : ℚ) * a ≤ u)
    (hz : 0 ≤ z) (k : ℕ) :
    ⌈(B : ℚ) * (a * z / k)⌉ ≤ upperDiv u z k := by
  rw [upperDiv_eq]
  apply Int.ceil_mono
  calc
    (B : ℚ) * (a * z / k) = ((B : ℚ) * a) * z / k := by ring
    _ ≤ (u : ℚ) * z / k :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by exact_mod_cast hz))
        (Nat.cast_nonneg k)

theorem rounded_of_integer {q t r : ℕ} {values upper : List ℤ} {A : ℚ} {P B : ℤ}
    (hlen : values.length = q) (hP : 0 ≤ P)
    (he : ∀ i : Fin r, (B : ℚ) * A ^ i.val ≤ upper.getD i.val 0)
    (hm : Nat.clog 2 (t * q) < r) (h : IntegerRounded q t values upper P B) :
    Rounded q values (t * q) P A B := by
  have hev (k : ℕ) (hk : k ≤ t * q) :
      (B : ℚ) * dyadicEnvelope A k ≤ upper.getD (Nat.clog 2 k) 0 :=
    he ⟨_, lt_of_le_of_lt (Nat.clog_mono_right 2 hk) hm⟩
  unfold IntegerRounded at h
  simp only [sumList_eq, repeatValues_length, hlen, zero_add] at h
  have ht : ∀ k ∈ range (t * q),
      (repeatValues values t).getD k 0 = tableValue q values k := by
    intro k hk
    simpa only [tableValue, hlen] using
      repeatValues_getD values t k (by simpa only [hlen] using mem_range.mp hk)
  have hupper := sum_congr rfl (fun (k : ℕ) hk => congrArg
    (fun v : ℤ => upperDiv (upper.getD (Nat.clog 2 k) 0) (max (-v) 0) k) (ht k hk))
  have hlower := sum_congr rfl (fun (k : ℕ) hk => congrArg
    (fun v : ℤ => B * max v 0 / (k : ℤ)) (ht k hk))
  rw [hupper, hlower] at h
  have hu :
      (∑ k ∈ range (t * q),
        ⌈(B : ℚ) * (dyadicEnvelope A k * (max (-(tableValue q values k)) 0 : ℚ) / k)⌉) ≤
      ∑ k ∈ range (t * q),
        upperDiv (upper.getD (Nat.clog 2 k) 0) (max (-(tableValue q values k)) 0) k := by
    apply sum_le_sum
    intro k hk
    simpa only [Int.cast_max, Int.cast_neg, Int.cast_zero] using
      ceil_weight_le (z := max (-(tableValue q values k)) 0)
        (hev k (le_of_lt (mem_range.mp hk))) (le_max_right _ _) k
  have htail :
      ⌈(B : ℚ) * ((P : ℚ) * dyadicEnvelope A (t * q) / (t * q))⌉ ≤
      upperDiv (upper.getD (Nat.clog 2 (t * q)) 0) P (t * q) := by
    simpa only [mul_comm (P : ℚ), Nat.cast_mul] using
      ceil_weight_le (hev _ le_rfl) hP (t * q)
  have hl :
      (∑ k ∈ range (t * q), B * max (tableValue q values k) 0 / (k : ℤ)) =
      ∑ k ∈ range (t * q),
        ⌊(B : ℚ) * ((max (tableValue q values k) 0 : ℚ) / k)⌋ := by
    apply sum_congr rfl
    intro k _
    simpa only [Int.cast_max, Int.cast_zero, mul_div_assoc] using
      lowerDiv_eq B (max (tableValue q values k) 0) k
  unfold Rounded
  simpa only [Nat.cast_mul] using (lt_of_le_of_lt (add_le_add hu htail) h).trans_eq hl

theorem weighted_of_integer {q t r : ℕ} {values upper : List ℤ} {A : ℚ} {P B : ℤ}
    (hlen : values.length = q) (hp : prefixList P 0 values = true) (hP : 0 ≤ P)
    (hB : 0 < B) (he : ∀ i : Fin r, (B : ℚ) * A ^ i.val ≤ upper.getD i.val 0)
    (hm : Nat.clog 2 (t * q) < r) (h : IntegerRounded q t values upper P B) :
    VerifiedScan.Weighted q values (t * q) P A :=
  weighted_of_rounded (prefixCheck_of_prefixList hlen hp) (by exact_mod_cast hB)
    (rounded_of_integer hlen hP he hm h)

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
