import LiuWang.Proof.NearOneDensity.Correlation
import LiuWang.Proof.NearOneDensity.Clustering
import LiuWang.Proof.NearOneDensity.Multiplicity

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NearOneDensity

def zeroValues {q : ℕ} [NeZero q] (χ : Character q) (α y : ℝ) : Finset ℂ :=
  (finite_ordinary_zero_window χ y).toFinset.filter (fun ρ => α ≤ ρ.re)

abbrev ZeroIndex (q : ℕ) [NeZero q] :=
  Σ χ : Character q, Σ ρ : ℂ, Fin (analyticOrderNatAt χ.LFunction ρ)

def zeroFamily (q : ℕ) [NeZero q] (α y : ℝ) : Finset (ZeroIndex q) :=
  Finset.univ.sigma (fun χ => (zeroValues χ α y).sigma (fun _ρ => Finset.univ))

def zeroCount (q : ℕ) [NeZero q] (α y : ℝ) : ℕ :=
  (zeroFamily q α y).card

theorem zeroCount_eq_multiplicity_sum (q : ℕ) [NeZero q] (α y : ℝ) :
    zeroCount q α y =
      ∑ χ : Character q, ∑ ρ ∈ zeroValues χ α y, analyticOrderNatAt χ.LFunction ρ := by
  simp [zeroCount, zeroFamily, Finset.card_sigma]

theorem mem_zeroValues {q : ℕ} [NeZero q] {χ : Character q} {α y : ℝ}
    (hα : 1 / 2 ≤ α) {ρ : ℂ} :
    ρ ∈ zeroValues χ α y ↔
      χ.LFunction ρ = 0 ∧ α ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ y := by
  rw [zeroValues, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨hz, _, hlt, hy⟩, hge⟩
    exact ⟨hz, hge, hlt, hy⟩
  · rintro ⟨hz, hge, hlt, hy⟩
    exact ⟨⟨hz, hα.trans hge, hlt, hy⟩, hge⟩

theorem mem_zeroFamily {q : ℕ} [NeZero q] {α y : ℝ}
    (hα : 1 / 2 ≤ α) (p : ZeroIndex q) :
    p ∈ zeroFamily q α y ↔
      p.1.LFunction p.2.1 = 0 ∧ α ≤ p.2.1.re ∧ p.2.1.re < 1 ∧ |p.2.1.im| ≤ y := by
  simp only [zeroFamily, Finset.mem_sigma, Finset.mem_univ, true_and, and_true]
  exact mem_zeroValues hα

theorem source_alpha_ge_half {z lam : ℝ} (hz : 100000000000 ≤ z) (hlam : lam ≤ 0.5) :
    1 / 2 ≤ 1 - lam / Real.log z := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : 4 ≤ z)
  have hL : 1 ≤ Real.log z := by linarith [Real.log_two_gt_d9]
  have hdiv : lam / Real.log z ≤ 1 / 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

theorem source_mem_zeroFamily {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hlam : lam ≤ 0.5) (p : ZeroIndex q) :
    p ∈ zeroFamily q (1 - lam / Real.log z) y ↔
      p.1.LFunction p.2.1 = 0 ∧ 1 - lam / Real.log z ≤ p.2.1.re ∧
        p.2.1.re < 1 ∧ |p.2.1.im| ≤ y :=
  mem_zeroFamily (source_alpha_ge_half hz hlam) p

theorem ordinary_zero_has_index {q : ℕ} [NeZero q] {χ : Character q} {α y : ℝ}
    (hα : 1 / 2 ≤ α) {ρ : ℂ}
    (hz : χ.LFunction ρ = 0) (hre : α ≤ ρ.re) (hlt : ρ.re < 1) (hy : |ρ.im| ≤ y) :
    ∃ p ∈ zeroFamily q α y, p.1 = χ ∧ p.2.1 = ρ := by
  have hp := ordinary_zero_multiplicity_pos χ
    (show ρ ≠ 1 by intro h; simp [h] at hlt) hz
  exact ⟨⟨χ, ρ, ⟨0, hp⟩⟩, (mem_zeroFamily hα _).mpr ⟨hz, hre, hlt, hy⟩, rfl, rfl⟩

theorem actual_zero_quadratic {q : ℕ} [NeZero q] (α y : ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1) :
    (∑ p ∈ zeroFamily q α y, logKernel σ τ c p.1 p.2.1.im) ^ 2 ≤
      (∑' n, dampedWeight σ τ c n) *
        ∑ p ∈ zeroFamily q α y, ∑ r ∈ zeroFamily q α y,
          logKernel σ τ c (quotientCharacter p.1 r.1) (p.2.1.im - r.2.1.im) :=
  logKernel_quadratic (zeroFamily q α y) (fun p => p.1) (fun p => p.2.1.im)
    hσ hτ hστ hc

theorem actual_zero_count_of_logKernel {q : ℕ} [NeZero q] (α y : ℝ)
    {σ τ c A B D : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1)
    (hA : 0 ≤ A) (hBA : B ≤ A) (hD : 0 ≤ D)
    (hmass : (∑' n, dampedWeight σ τ c n) ≤ A)
    (hzero : ∀ p ∈ zeroFamily q α y, logKernel σ τ c p.1 p.2.1.im ≤ -D)
    (hoff : ∀ p ∈ zeroFamily q α y, ∀ r ∈ zeroFamily q α y, p ≠ r →
      logKernel σ τ c (quotientCharacter p.1 r.1) (p.2.1.im - r.2.1.im) ≤ B)
    (hgap : 0 < D ^ 2 - A * B) :
    (zeroCount q α y : ℝ) ≤ (A ^ 2 - A * B) / (D ^ 2 - A * B) :=
  count_of_logKernel (zeroFamily q α y) (fun p => p.1) (fun p => p.2.1.im)
    hσ hτ hστ hc hA hBA hD hmass hzero hoff hgap

theorem actual_zero_cluster_selection {q : ℕ} [NeZero q] (α y : ℝ)
    {b : ℝ} (hb : 0 ≤ b) (m : ℕ)
    (hlocal : ∀ χ t, ((zeroFamily q α y).filter
      (fun p => p.1 = χ ∧ |p.2.1.im - t| ≤ b)).card ≤ m) :
    ∃ u ⊆ zeroFamily q α y, zeroCount q α y ≤ m * u.card ∧
      ∀ p ∈ u, ∀ r ∈ u, p ≠ r → p.1 = r.1 → 2 * b < |p.2.1.im - r.2.1.im| :=
  exists_separated_subfamily (zeroFamily q α y) (fun p => p.1) (fun p => p.2.1.im)
    hb m hlocal

end LiuWang.Proof.NearOneDensity
