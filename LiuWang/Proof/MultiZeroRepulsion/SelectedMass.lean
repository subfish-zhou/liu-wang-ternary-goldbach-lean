import LiuWang.Proof.ZeroRegionFamily.Sharp.ZeroSumBudget
import LiuWang.Proof.DirichletZeroCount.Family

/-! Finite, multiplicity-preserving selections from the actual full Stechkin sums. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion

theorem reflected_finset_sum_le {ι : Type*} [DecidableEq ι] (e : ι ≃ ι)
    (he : Function.Involutive e) (f : ι → ℝ) (hf : Summable f)
    (hn : ∀ p, 0 ≤ f p + f (e p)) (s : Finset ι)
    (hd : Disjoint s (s.image e)) :
    ∑ p ∈ s, (f p + f (e p)) ≤ ∑' p, f p := by
  let g p := f p + f (e p)
  have hc : Summable (fun p => f (e p)) := e.summable_iff.mpr hf
  have hg : Summable g := hf.add hc
  have hsum := hg.sum_le_tsum (s ∪ s.image e) (fun p _ => hn p)
  change (∑ p ∈ s ∪ s.image e, g p) ≤ ∑' p, g p at hsum
  rw [Finset.sum_union hd, Finset.sum_image (fun _ _ _ _ h => e.injective h)] at hsum
  have hi (p : ι) : g (e p) = g p := by dsimp [g]; rw [he]; ring
  simp_rw [hi] at hsum
  have ht : (∑' p, g p) = 2 * ∑' p, f p := by
    dsimp [g]
    rw [hf.tsum_add hc, e.tsum_eq]
    ring
  rw [ht] at hsum
  change ∑ p ∈ s, g p ≤ _
  linarith

theorem primitive_selected_mass_le {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {sigma : ℝ} (hs : 1 < sigma)
    (t : ℝ) (s : Finset (SymmetricCompletedZeroIndex chi))
    (hr : ∀ p ∈ s, 1 / 2 < (Complex.Hadamard.divisorZeroIndex₀_val p).re) :
    (∑ p ∈ s, (dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val p) +
      dampedZeroKernel sigma t (1 - conj (Complex.Hadamard.divisorZeroIndex₀_val p)))) ≤
        primitiveZeroSum chi sigma t := by
  let e := symmetricCompletedZeroReflectionEquiv hc hp
  have hd : Disjoint s (s.image e) := by
    rw [Finset.disjoint_left]
    intro p hps hpi
    obtain ⟨r, hrs, he⟩ := Finset.mem_image.mp hpi
    have hvr := symmetricCompletedZeroReflectionEquiv_val hc hp r
    change Complex.Hadamard.divisorZeroIndex₀_val (e r) = _ at hvr
    rw [he] at hvr
    have hh := congrArg Complex.re hvr
    simp only [sub_re, one_re, conj_re] at hh
    linarith [hr p hps, hr r hrs]
  have hh := reflected_finset_sum_le e (symmetricCompletedZeroReflection_involutive hc hp)
    (fun p => dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val p))
    (summable_dampedZeroKernel hc hp hs t) (fun p => by
      dsimp [e]
      rw [symmetricCompletedZeroReflectionEquiv_val]
      have hz := symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hc hp p
      exact dampedZeroKernel_pair_nonneg hs t ⟨hz.1.le, hz.2.le⟩) s hd
  simpa only [e, symmetricCompletedZeroReflectionEquiv_val, primitiveZeroSum] using hh

theorem primitive_selected_bound {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ)
    (s : Finset (SymmetricCompletedZeroIndex chi))
    (hr : ∀ p ∈ s, 1 / 2 < (Complex.Hadamard.divisorZeroIndex₀_val p).re) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
      (∑ p ∈ s, (dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val p) +
        dampedZeroKernel sigma t (1 - conj (Complex.Hadamard.divisorZeroIndex₀_val p)))) ≤
      stechkinConductorCoeff * (Real.log q + Real.log (max 1 |t|) - Real.log Real.pi) + 4 / 15 := by
  have hh := primitive_full_zero_sum_bound hc hp hs hs1 t
  linarith [primitive_selected_mass_le hc hp hs t s hr]

theorem primitive_same_height_selected_bound {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ)
    (s : Finset (SymmetricCompletedZeroIndex chi))
    (hr : ∀ p ∈ s, 1 / 2 < (Complex.Hadamard.divisorZeroIndex₀_val p).re)
    (ht : ∀ p ∈ s, (Complex.Hadamard.divisorZeroIndex₀_val p).im = t) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
      (∑ p ∈ s, 1 / (sigma - (Complex.Hadamard.divisorZeroIndex₀_val p).re)) ≤
      stechkinConductorCoeff * (Real.log q + Real.log (max 1 |t|) - Real.log Real.pi) + 4 / 15 := by
  apply le_trans _ (primitive_selected_bound hc hp hs hs1 t s hr)
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro p hps
  have hh := selected_pair_dominates hs
    (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hc hp p)
  simpa only [ht p hps] using hh

theorem xi_selected_mass_le {sigma : ℝ} (hs : 1 < sigma) (t : ℝ)
    (s : Finset RiemannXiDivisorZeroIndex)
    (hr : ∀ p ∈ s, 1 / 2 < (riemannXiDivisorZeroValue p).re) :
    (∑ p ∈ s, (dampedZeroKernel sigma t (riemannXiDivisorZeroValue p) +
      dampedZeroKernel sigma t (1 - conj (riemannXiDivisorZeroValue p)))) ≤
        zetaZeroSum sigma t := by
  have hf : Summable (fun p : RiemannXiDivisorZeroIndex =>
      dampedZeroKernel sigma t (riemannXiDivisorZeroValue p)) :=
    (xi_raw_summable (by simpa [Complex.mul_re] using hs.le)).sub
      ((xi_raw_summable (by simpa [Complex.mul_re] using
        (hs.trans_le (stechkinSigma_ge hs)).le)).mul_left stechkinK)
  have hd : Disjoint s (s.image xiReflection) := by
    rw [Finset.disjoint_left]
    intro p hps hpi
    obtain ⟨r, hrs, he⟩ := Finset.mem_image.mp hpi
    have hvr := xiReflect_val r
    change riemannXiDivisorZeroValue (xiReflection r) = _ at hvr
    rw [he] at hvr
    have hh := congrArg Complex.re hvr
    simp only [sub_re, one_re, conj_re] at hh
    linarith [hr p hps, hr r hrs]
  have hh := reflected_finset_sum_le xiReflection xiReflect_involutive
    (fun p => dampedZeroKernel sigma t (riemannXiDivisorZeroValue p)) hf (fun p => by
      change 0 ≤ dampedZeroKernel sigma t (riemannXiDivisorZeroValue p) +
        dampedZeroKernel sigma t (1 - conj (riemannXiDivisorZeroValue p))
      have hz := riemannXiDivisorZeroValue_re_mem_Ioo p
      exact dampedZeroKernel_pair_nonneg hs t ⟨hz.1.le, hz.2.le⟩) s hd
  exact hh

theorem zeta_selected_bound {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ)
    (s : Finset RiemannXiDivisorZeroIndex)
    (hr : ∀ p ∈ s, 1 / 2 < (riemannXiDivisorZeroValue p).re) :
    zetaDamped sigma t +
      (∑ p ∈ s, (dampedZeroKernel sigma t (riemannXiDivisorZeroValue p) +
        dampedZeroKernel sigma t (1 - conj (riemannXiDivisorZeroValue p)))) ≤
      poleDifference sigma t + stechkinConductorCoeff * (Real.log (max 1 |t|) - Real.log Real.pi) +
        23 / 40 - 11 * stechkinK / 30 := by
  have hi := zeta_full_zero_sum_identity hs t
  have hg := shiftedGamma_all_height hs hs1 t
  linarith [xi_selected_mass_le hs t s hr]

end LiuWang.Proof.MultiZeroRepulsion