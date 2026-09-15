import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.ListBounds

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

def CachedRounded (q t : ℕ) (values : List ℤ) (P B : ℚ) (powers : List ℚ) : Prop :=
  sumList (fun k v =>
      ⌈B * (powers.getD (Nat.clog 2 k) 0 * (max (-v) 0 : ℚ) / k)⌉)
      0 (repeatValues values t) +
    ⌈B * (P * powers.getD (Nat.clog 2 (t * q)) 0 / (t * q))⌉ <
  sumList (fun k v => ⌊B * ((max v 0 : ℚ) / k)⌋) 0 (repeatValues values t)

instance (q t : ℕ) (values : List ℤ) (P B : ℚ) (powers : List ℚ) :
    Decidable (CachedRounded q t values P B powers) := by
  unfold CachedRounded
  infer_instance

theorem listRounded_of_cached {q t r : ℕ} {values : List ℤ} {P A B : ℚ}
    {powers : List ℚ} (hlen : values.length = q)
    (hpowers : ∀ i : Fin r, powers.getD i.val 0 = A ^ i.val)
    (hm : Nat.clog 2 (t * q) < r) (h : CachedRounded q t values P B powers) :
    ListRounded q t values P A B := by
  have he (k : ℕ) (hk : k ≤ t * q) :
      powers.getD (Nat.clog 2 k) 0 = dyadicEnvelope A k :=
    hpowers ⟨_, lt_of_le_of_lt (Nat.clog_mono_right 2 hk) hm⟩
  have hs :
      sumList (fun k v =>
          ⌈B * (powers.getD (Nat.clog 2 k) 0 * (max (-v) 0 : ℚ) / k)⌉)
          0 (repeatValues values t) =
      sumList (fun k v => ⌈B * (dyadicEnvelope A k * (max (-v) 0 : ℚ) / k)⌉)
          0 (repeatValues values t) := by
    simp only [sumList_eq, repeatValues_length, hlen, zero_add]
    apply sum_congr rfl
    intro k hk
    rw [he k (le_of_lt (mem_range.mp hk))]
  unfold CachedRounded at h
  rw [hs, he _ le_rfl] at h
  exact h

theorem weighted_of_cached {q t r : ℕ} {values : List ℤ} {P A B : ℚ}
    {powers : List ℚ} (hlen : values.length = q)
    (hp : prefixList P 0 values = true) (hB : 0 < B)
    (hpowers : ∀ i : Fin r, powers.getD i.val 0 = A ^ i.val)
    (hm : Nat.clog 2 (t * q) < r) (h : CachedRounded q t values P B powers) :
    VerifiedScan.Weighted q values (t * q) P A :=
  weighted_of_list hlen hp hB (listRounded_of_cached hlen hpowers hm h)

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
