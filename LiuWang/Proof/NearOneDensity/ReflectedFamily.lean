import LiuWang.Proof.ZeroRegionFamily.Sharp.ZeroSumBudget
import LiuWang.Proof.NearOneDensity.Clustering

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Classical
open Complex BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity

theorem finite_reflected_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι ≃ ι)
    (he : Function.Involutive e) (f : ι → ℝ) (hf : Summable f)
    (hpos : ∀ i, 0 ≤ f i + f (e i))
    (hdisj : Disjoint s (s.image e)) :
    (∑ i ∈ s, (f i + f (e i))) ≤ ∑' i, f i := by
  let g := fun i => f i + f (e i)
  have hcomp : Summable (fun i => f (e i)) := e.summable_iff.mpr hf
  have hsum := (hf.add hcomp).sum_le_tsum (s ∪ s.image e) (fun i _ => hpos i)
  have hg : ∀ i, g (e i) = g i := by intro i; dsimp [g]; rw [he i]; ring
  change ∑ i ∈ s ∪ s.image e, g i ≤ ∑' i, g i at hsum
  rw [Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h => e.injective h)] at hsum
  simp only [hg] at hsum
  have htotal : (∑' i, g i) = 2 * ∑' i, f i := by
    dsimp [g]
    rw [hf.tsum_add hcomp, e.tsum_eq f]
    ring
  rw [htotal] at hsum
  linarith

theorem primitive_finite_reflected_sum_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (s : Finset (SymmetricCompletedZeroIndex χ))
    (hr : ∀ p ∈ s, 1 / 2 < (Hadamard.divisorZeroIndex₀_val p).re)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (∑ p ∈ s, (dampedZeroKernel σ t (Hadamard.divisorZeroIndex₀_val p) +
      dampedZeroKernel σ t (1 - conj (Hadamard.divisorZeroIndex₀_val p)))) ≤
        primitiveZeroSum χ σ t := by
  let e := symmetricCompletedZeroReflectionEquiv hχ hp
  let f := fun p : SymmetricCompletedZeroIndex χ =>
    dampedZeroKernel σ t (Hadamard.divisorZeroIndex₀_val p)
  have hn : ∀ p, 0 ≤ f p + f (e p) := by
    intro p
    dsimp [f, e]
    rw [symmetricCompletedZeroReflectionEquiv_val]
    have hh := symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hχ hp p
    exact dampedZeroKernel_pair_nonneg hσ t ⟨hh.1.le, hh.2.le⟩
  have hd : Disjoint s (s.image e) := by
    apply Finset.disjoint_left.mpr
    intro p hps hpi
    obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hpi
    have hj := hr j hjs
    have hh := hr (e j) hps
    dsimp [e] at hh
    rw [symmetricCompletedZeroReflectionEquiv_val] at hh
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hh
    linarith
  have h := finite_reflected_sum_le s e
    (symmetricCompletedZeroReflection_involutive hχ hp) f
    (summable_dampedZeroKernel hχ hp hσ t) hn hd
  simpa only [f, e, symmetricCompletedZeroReflectionEquiv_val, primitiveZeroSum] using h

theorem primitive_finite_reflected_budget {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (s : Finset (SymmetricCompletedZeroIndex χ))
    (hr : ∀ p ∈ s, 1 / 2 < (Hadamard.divisorZeroIndex₀_val p).re)
    {σ : ℝ} (hσ : 1 < σ) (hσ₁ : σ ≤ 23 / 20) (t : ℝ) :
    dampedLogDeriv χ σ (stechkinSigma σ) stechkinK t +
      (∑ p ∈ s, (dampedZeroKernel σ t (Hadamard.divisorZeroIndex₀_val p) +
        dampedZeroKernel σ t (1 - conj (Hadamard.divisorZeroIndex₀_val p)))) ≤
      stechkinConductorCoeff * (Real.log q + Real.log (max 1 |t|) - Real.log Real.pi) + 4 / 15 := by
  linarith [primitive_finite_reflected_sum_le hχ hp s hr hσ t,
    primitive_full_zero_sum_bound hχ hp hσ hσ₁ t]

end LiuWang.Proof.NearOneDensity
