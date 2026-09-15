import LiuWang.Proof.NearOneDensity.WindowOccupancy
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLFunctionOrder
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionOrder

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical Complex BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NearOneDensity

def ordinaryWindowValues {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (α y t b : ℝ) : Finset ℂ :=
  (zeroValues χ α y).filter (fun ρ => |ρ.im - t| ≤ b)

def ordinaryWindowCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (α y t b : ℝ) : ℕ :=
  ∑ ρ ∈ ordinaryWindowValues χ α y t b, analyticOrderNatAt χ.LFunction ρ

theorem ordinaryWindowCount_eq_family_filter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (α y t b : ℝ) :
    ordinaryWindowCount χ α y t b =
      ((zeroFamily q α y).filter (fun p => p.1 = χ ∧ |p.2.1.im - t| ≤ b)).card := by
  simp [ordinaryWindowCount, ordinaryWindowValues, zeroFamily, Finset.filter_sigma,
    Finset.card_sigma, Finset.sum_filter, Finset.filter_const, ite_and, apply_ite,
    Finset.sum_ite_irrel]

def inducingWindowIndices {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (v : Finset ℂ) :
    Finset (SymmetricCompletedZeroIndex χ.primitiveCharacter) :=
  v.biUnion (fun ρ => Hadamard.divisorZeroIndex₀_fiberFinset
    (symmetricCompletedLFunction χ.primitiveCharacter) ρ)

theorem mem_inducingWindowIndices {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (v : Finset ℂ)
    (p : SymmetricCompletedZeroIndex χ.primitiveCharacter) :
    p ∈ inducingWindowIndices χ v ↔ Hadamard.divisorZeroIndex₀_val p ∈ v := by
  simp [inducingWindowIndices, Hadamard.mem_divisorZeroIndex₀_fiberFinset]

theorem inducingWindowIndices_card {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1)
    (v : Finset ℂ) (hv : ∀ ρ ∈ v, 0 < ρ.re) :
    (inducingWindowIndices χ v).card = ∑ ρ ∈ v, analyticOrderNatAt χ.LFunction ρ := by
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one χ hχ
  unfold inducingWindowIndices
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
      (differentiable_symmetricCompletedLFunction hpr)
      (show ρ ≠ 0 by intro hh; simpa [hh] using hv ρ hρ),
      analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hpr (hv ρ hρ),
      analyticOrderNatAt_LFunction_eq_primitive χ hχ (hv ρ hρ)]
  · intro ρ _ τ _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rw [Hadamard.mem_divisorZeroIndex₀_fiberFinset] at hp hq
    exact hne (hp.symm.trans hq)

theorem nonprincipal_row_window_count (r : DensityRow) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {z lam y t : ℝ} (hz : 100000000000 ≤ z) (hlam : 0 ≤ lam)
    (hlam₁ : lam ≤ rowLambda r)
    (hheight : Real.log χ.conductor + Real.log (max 1 |t|) ≤ Real.log z + 1 / 10) :
    ordinaryWindowCount χ (1 - lam / Real.log z) y t (rowRadius r / Real.log z) ≤
      rowMultiplicity r := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let v := ordinaryWindowValues χ (1 - lam / Real.log z) y t (rowRadius r / Real.log z)
  have hL : 25 ≤ Real.log z := by linarith [source_log_lower hz]
  have hmax : rowLambda r ≤ 0.5 := by cases r <;> norm_num [rowLambda]
  have hα := source_alpha_ge_half hz (hlam₁.trans hmax)
  have hmem (ρ) (hρ : ρ ∈ v) := (mem_zeroValues hα).mp (Finset.mem_filter.mp hρ).1
  have hcard := inducingWindowIndices_card χ hχ v
    (fun ρ hρ => by linarith [(hmem ρ hρ).2.1])
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one χ hχ
  have hc := primitive_row_window_count r hpr χ.primitiveCharacter_isPrimitive
    (inducingWindowIndices χ v) hL hlam hlam₁ hheight
    (fun p hp => (hmem _ ((mem_inducingWindowIndices χ v p).mp hp)).2.1)
    (fun p hp => by
      have hh := (Finset.mem_filter.mp ((mem_inducingWindowIndices χ v p).mp hp)).2
      simpa only [abs_sub_comm] using hh)
  rw [hcard] at hc
  exact hc

end LiuWang.Proof.NearOneDensity
