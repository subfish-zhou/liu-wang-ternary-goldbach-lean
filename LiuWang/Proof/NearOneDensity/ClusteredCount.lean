import LiuWang.Proof.NearOneDensity.ActualZeros

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NearOneDensity

/-- The local occupancy cost `m` is paid once, after applying the quadratic
method to the selected family. In particular `m = 2` does not introduce 4. -/
theorem actual_zero_count_of_clustered_logKernel {q : ℕ} [NeZero q] (α y : ℝ)
    {b : ℝ} (hb : 0 ≤ b) (m : ℕ)
    (hlocal : ∀ χ t, ((zeroFamily q α y).filter
      (fun p => p.1 = χ ∧ |p.2.1.im - t| ≤ b)).card ≤ m)
    {σ τ c A B D : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1)
    (hA : 0 ≤ A) (hBA : B ≤ A) (hD : 0 ≤ D)
    (hmass : (∑' n, dampedWeight σ τ c n) ≤ A)
    (hzero : ∀ p ∈ zeroFamily q α y, logKernel σ τ c p.1 p.2.1.im ≤ -D)
    (hoff : ∀ p ∈ zeroFamily q α y, ∀ r ∈ zeroFamily q α y,
      p.1 ≠ r.1 ∨ 2 * b < |p.2.1.im - r.2.1.im| →
      logKernel σ τ c (quotientCharacter p.1 r.1) (p.2.1.im - r.2.1.im) ≤ B)
    (hgap : 0 < D ^ 2 - A * B) :
    (zeroCount q α y : ℝ) ≤ m * ((A ^ 2 - A * B) / (D ^ 2 - A * B)) := by
  obtain ⟨u, hu, hcard, hsep⟩ := actual_zero_cluster_selection α y hb m hlocal
  have hcount := count_of_logKernel u (fun p => p.1) (fun p => p.2.1.im)
    hσ hτ hστ hc hA hBA hD hmass (fun p hp => hzero p (hu hp))
    (fun p hp r hr hpr => hoff p (hu hp) r (hu hr) (by
      by_cases hχ : p.1 = r.1
      · exact Or.inr (hsep p hp r hr hpr hχ)
      · exact Or.inl hχ)) hgap
  calc
    _ ≤ (m : ℝ) * u.card := by exact_mod_cast hcard
    _ ≤ _ := mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg m)

theorem actual_zero_count_le_mul_of_clustered_logKernel {q : ℕ} [NeZero q] (α y : ℝ)
    {b : ℝ} (hb : 0 ≤ b) (m K : ℕ)
    (hlocal : ∀ χ t, ((zeroFamily q α y).filter
      (fun p => p.1 = χ ∧ |p.2.1.im - t| ≤ b)).card ≤ m)
    {σ τ c A B D : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1)
    (hA : 0 ≤ A) (hBA : B ≤ A) (hD : 0 ≤ D)
    (hmass : (∑' n, dampedWeight σ τ c n) ≤ A)
    (hzero : ∀ p ∈ zeroFamily q α y, logKernel σ τ c p.1 p.2.1.im ≤ -D)
    (hoff : ∀ p ∈ zeroFamily q α y, ∀ r ∈ zeroFamily q α y,
      p.1 ≠ r.1 ∨ 2 * b < |p.2.1.im - r.2.1.im| →
      logKernel σ τ c (quotientCharacter p.1 r.1) (p.2.1.im - r.2.1.im) ≤ B)
    (hgap : 0 < D ^ 2 - A * B)
    (hbudget : (A ^ 2 - A * B) / (D ^ 2 - A * B) < K + 1) :
    zeroCount q α y ≤ m * K := by
  obtain ⟨u, hu, hcard, hsep⟩ := actual_zero_cluster_selection α y hb m hlocal
  have hcount := count_of_logKernel u (fun p => p.1) (fun p => p.2.1.im)
    hσ hτ hστ hc hA hBA hD hmass (fun p hp => hzero p (hu hp))
    (fun p hp r hr hpr => hoff p (hu hp) r (hu hr) (by
      by_cases hχ : p.1 = r.1
      · exact Or.inr (hsep p hp r hr hpr hχ)
      · exact Or.inl hχ)) hgap
  have hsmall : u.card < K + 1 := by exact_mod_cast hcount.trans_lt hbudget
  exact hcard.trans (Nat.mul_le_mul_left m (Nat.lt_succ_iff.mp hsmall))

end LiuWang.Proof.NearOneDensity
