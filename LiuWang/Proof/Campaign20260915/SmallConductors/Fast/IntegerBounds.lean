import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Prefix

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.SmallConductorExpansion
open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

def Rounded (q : ℕ) (values : List ℤ) (m : ℕ) (P A B : ℚ) : Prop :=
  (∑ k ∈ range m,
      ⌈B * (dyadicEnvelope A k * (max (-(tableValue q values k)) 0 : ℚ) / k)⌉) +
    ⌈B * (P * dyadicEnvelope A m / m)⌉ <
      ∑ k ∈ range m, ⌊B * ((max (tableValue q values k) 0 : ℚ) / k)⌋

instance (q : ℕ) (values : List ℤ) (m : ℕ) (P A B : ℚ) :
    Decidable (Rounded q values m P A B) := by
  unfold Rounded
  infer_instance

theorem sum_lt_of_rounded {m : ℕ} {f g : ℕ → ℚ} {t B : ℚ} (hB : 0 < B)
    (h : (∑ k ∈ range m, ⌈B * f k⌉) + ⌈B * t⌉ <
      ∑ k ∈ range m, ⌊B * g k⌋) :
    (∑ k ∈ range m, f k) + t < ∑ k ∈ range m, g k := by
  have hu : (∑ k ∈ range m, B * f k) + B * t ≤
      (∑ k ∈ range m, (⌈B * f k⌉ : ℚ)) + (⌈B * t⌉ : ℚ) :=
    add_le_add (sum_le_sum fun k _ => Int.le_ceil _) (Int.le_ceil _)
  have hl : (∑ k ∈ range m, (⌊B * g k⌋ : ℚ)) ≤
      ∑ k ∈ range m, B * g k :=
    sum_le_sum fun k _ => Int.floor_le _
  have hh : (∑ k ∈ range m, (⌈B * f k⌉ : ℚ)) + (⌈B * t⌉ : ℚ) <
      ∑ k ∈ range m, (⌊B * g k⌋ : ℚ) := by exact_mod_cast h
  have hb := lt_of_le_of_lt hu (lt_of_lt_of_le hh hl)
  simpa only [← mul_sum, ← mul_add, mul_lt_mul_iff_right₀ hB] using hb

theorem weighted_of_rounded {q m : ℕ} {values : List ℤ} {P A B : ℚ}
    (hp : VerifiedScan.prefixCheck q values P = true) (hB : 0 < B)
    (h : Rounded q values m P A B) :
    VerifiedScan.Weighted q values m P A :=
  ⟨hp, sum_lt_of_rounded hB h⟩

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
