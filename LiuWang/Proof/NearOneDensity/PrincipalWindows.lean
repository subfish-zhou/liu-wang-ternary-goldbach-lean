import LiuWang.Proof.NearOneDensity.XiWindows

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical Complex BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.PrincipalPsi.Quantitative

namespace LiuWang.Proof.NearOneDensity

def xiWindowIndices (v : Finset ℂ) : Finset RiemannXiDivisorZeroIndex :=
  v.biUnion (Hadamard.divisorZeroIndex₀_fiberFinset riemannXi)

theorem mem_xiWindowIndices (v : Finset ℂ) (p : RiemannXiDivisorZeroIndex) :
    p ∈ xiWindowIndices v ↔ riemannXiDivisorZeroValue p ∈ v := by
  simp [xiWindowIndices, Hadamard.mem_divisorZeroIndex₀_fiberFinset,
    riemannXiDivisorZeroValue]

theorem xiWindowIndices_card {q : ℕ} [NeZero q] (v : Finset ℂ)
    (hv : ∀ ρ ∈ v, 0 < ρ.re ∧ ρ.re < 1) :
    (xiWindowIndices v).card =
      ∑ ρ ∈ v, analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction ρ := by
  unfold xiWindowIndices
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
      differentiable_riemannXi
      (show ρ ≠ 0 by intro hh; simpa [hh] using (hv ρ hρ).1),
      analyticOrderNatAt_xi_eq_principal (q := q) (hv ρ hρ).1
      (show ρ ≠ 1 by intro hh; simpa [hh] using (hv ρ hρ).2)]
  · intro ρ _ τ _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rw [Hadamard.mem_divisorZeroIndex₀_fiberFinset] at hp hq
    exact hne (hp.symm.trans hq)

theorem principal_row_window_count (r : DensityRow) {q : ℕ} [NeZero q]
    {z lam y t : ℝ} (hz : 100000000000 ≤ z) (hlam : 0 ≤ lam)
    (hlam₁ : lam ≤ rowLambda r)
    (hheight : Real.log (max 1 |t|) ≤ Real.log z + 1 / 10) :
    ordinaryWindowCount (1 : DirichletCharacter ℂ q)
      (1 - lam / Real.log z) y t (rowRadius r / Real.log z) ≤ rowMultiplicity r := by
  let v := ordinaryWindowValues (1 : DirichletCharacter ℂ q)
    (1 - lam / Real.log z) y t (rowRadius r / Real.log z)
  have hL : 25 ≤ Real.log z := by linarith [source_log_lower hz]
  have hmax : rowLambda r ≤ 0.5 := by cases r <;> norm_num [rowLambda]
  have hα := source_alpha_ge_half hz (hlam₁.trans hmax)
  have hmem (ρ) (hρ : ρ ∈ v) := (mem_zeroValues hα).mp (Finset.mem_filter.mp hρ).1
  have hcard := xiWindowIndices_card (q := q) v
    (fun ρ hρ => ⟨by linarith [(hmem ρ hρ).2.1], (hmem ρ hρ).2.2.1⟩)
  have hc := xi_row_window_count r (xiWindowIndices v) hL hlam hlam₁ hheight
    (fun p hp => (hmem _ ((mem_xiWindowIndices v p).mp hp)).2.1)
    (fun p hp => by
      have hh := (Finset.mem_filter.mp ((mem_xiWindowIndices v p).mp hp)).2
      simpa only [abs_sub_comm] using hh)
  rw [hcard] at hc
  exact hc

end LiuWang.Proof.NearOneDensity
