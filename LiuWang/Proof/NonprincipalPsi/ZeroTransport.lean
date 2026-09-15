import LiuWang.Proof.FixedHeightZeroSum.HighZeros
import BombieriVinogradov.Helpers.ComplexAnalysis.DivisorIndexTransport
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.Multiplicity

/-!
# 非主字符的实际闭高零点运输

只在正实部使用有限 Euler 修正的阶数等式。闭高度与临界线等号均保留，
再按零点值的完整纤维计数运输求和，不识别或删除重复标签。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.FixedHeightZeroSum
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonprincipalPsi

theorem completedZeroValue_re_lt_one_of_pos {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    (p : CompletedZeroIndex chi) (hp : 0 < (completedZeroValue p).re) :
    (completedZeroValue p).re < 1 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  obtain ⟨r, hr⟩ :=
    BombieriVinogradov.ComplexAnalysis.exists_nonzeroDivisorIndex_of_multiplicity_eq
      (g := symmetricCompletedLFunction chi.primitiveCharacter) p
      (completedDivisorMultiplicity_eq_primitive chi hchi hp)
  have hprimitive :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hstrip := completedZeroValue_re_mem_Ioo hprimitive
    chi.primitiveCharacter_isPrimitive r
  change completedZeroValue r = completedZeroValue p at hr
  simpa only [hr] using hstrip.2

theorem mem_highZeroIndices_nonprincipal {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    (T : ℝ) (p : CompletedZeroIndex chi) :
    p ∈ highZeroIndices chi T ↔
      |(completedZeroValue p).im| ≤ T ∧ 1 / 2 ≤ (completedZeroValue p).re := by
  classical
  simp only [highZeroIndices, fixedZeroIndices, Finset.mem_filter]
  constructor
  · exact fun hp => ⟨hp.1.2, hp.2⟩
  · intro hp
    have hre : 0 < (completedZeroValue p).re := by linarith [hp.2]
    refine ⟨⟨mem_criticalStripZeroTruncation_iff.mpr
      ⟨hre, completedZeroValue_re_lt_one_of_pos hchi p hre, ?_⟩, hp.1⟩, hp.2⟩
    change |(completedZeroValue p).im| < T + 1
    linarith [hp.1]

def highZeroValues {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T : ℝ) :
    Finset ℂ := by
  classical
  exact (highZeroIndices chi T).image completedZeroValue

theorem highZeroValues_eq_primitive {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (hchi : chi ≠ 1) (T : ℝ) :
    highZeroValues chi T = highZeroValues chi.primitiveCharacter T := by
  classical
  have hprimitive :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  ext rho
  constructor
  · intro hrho
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
    have hparts := (mem_highZeroIndices_nonprincipal hchi T p).mp hp
    have hre : 0 < (completedZeroValue p).re := by linarith [hparts.2]
    obtain ⟨r, hr⟩ :=
      BombieriVinogradov.ComplexAnalysis.exists_nonzeroDivisorIndex_of_multiplicity_eq
        (g := symmetricCompletedLFunction chi.primitiveCharacter) p
        (completedDivisorMultiplicity_eq_primitive chi hchi hre)
    change completedZeroValue r = completedZeroValue p at hr
    apply Finset.mem_image.mpr
    refine ⟨r, (mem_highZeroIndices_nonprincipal hprimitive T r).mpr ?_, hr.trans hpv⟩
    simpa only [hr] using hparts
  · intro hrho
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
    have hparts := (mem_highZeroIndices_nonprincipal hprimitive T p).mp hp
    have hre : 0 < (completedZeroValue p).re := by linarith [hparts.2]
    obtain ⟨r, hr⟩ :=
      BombieriVinogradov.ComplexAnalysis.exists_nonzeroDivisorIndex_of_multiplicity_eq
        (g := symmetricCompletedLFunction chi) p
        (completedDivisorMultiplicity_eq_primitive chi hchi hre).symm
    change completedZeroValue r = completedZeroValue p at hr
    apply Finset.mem_image.mpr
    refine ⟨r, (mem_highZeroIndices_nonprincipal hchi T r).mpr ?_, hr.trans hpv⟩
    simpa only [hr] using hparts

theorem highZeroFiber_card {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ highZeroValues chi T) :
    ((highZeroIndices chi T).filter (fun p => completedZeroValue p = rho)).card =
      analyticOrderNatAt chi.LFunction rho := by
  classical
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  have hparts := (mem_highZeroIndices_nonprincipal hchi T p).mp hp
  have hre : 0 < rho.re := by rw [← hpv]; linarith [hparts.2]
  have hne : rho ≠ 0 := by intro h; simp [h] at hre
  have hf :
      (highZeroIndices chi T).filter (fun p => completedZeroValue p = rho) =
        Complex.Hadamard.divisorZeroIndex₀_fiberFinset
          (symmetricCompletedLFunction chi) rho := by
    ext r
    rw [Finset.mem_filter, mem_highZeroIndices_nonprincipal hchi,
      Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset]
    change ((_ ∧ _) ∧ completedZeroValue r = rho) ↔ completedZeroValue r = rho
    refine and_iff_right_of_imp ?_
    intro hv
    simpa only [hv, hpv] using hparts
  rw [hf, Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (differentiable_symmetricCompletedLFunction hchi) hne,
    analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hchi hre]

theorem sum_highZeroValues_multiplicity {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (T : ℝ) (f : ℂ → ℂ) :
    ∑ rho ∈ highZeroValues chi T,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * f rho =
      ∑ p ∈ highZeroIndices chi T, f (completedZeroValue p) := by
  classical
  have hf : ∀ rho ∈ highZeroValues chi T,
      ∑ p ∈ (highZeroIndices chi T).filter (fun p => completedZeroValue p = rho),
          f (completedZeroValue p) =
        (analyticOrderNatAt chi.LFunction rho : ℂ) * f rho := by
    intro rho hrho
    calc
      _ = ∑ _p ∈ (highZeroIndices chi T).filter
          (fun p => completedZeroValue p = rho), f rho := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      _ = _ := by simp [highZeroFiber_card hchi hrho]
  calc
    _ = ∑ rho ∈ highZeroValues chi T,
        ∑ p ∈ (highZeroIndices chi T).filter (fun p => completedZeroValue p = rho),
          f (completedZeroValue p) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact (hf rho hrho).symm
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (fun p => f (completedZeroValue p))

theorem sum_highZeroIndices_eq_primitive {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (hchi : chi ≠ 1) (T : ℝ) (f : ℂ → ℂ) :
    ∑ p ∈ highZeroIndices chi T, f (completedZeroValue p) =
      ∑ p ∈ highZeroIndices chi.primitiveCharacter T, f (completedZeroValue p) := by
  classical
  have hprimitive :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  rw [← sum_highZeroValues_multiplicity hchi,
    ← sum_highZeroValues_multiplicity hprimitive, highZeroValues_eq_primitive chi hchi]
  apply Finset.sum_congr rfl
  intro rho hrho
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  have hparts := (mem_highZeroIndices_nonprincipal hprimitive T p).mp hp
  have hre : 0 < rho.re := by rw [← hpv]; linarith [hparts.2]
  rw [analyticOrderNatAt_LFunction_eq_primitive chi hchi hre]

theorem highZeroSum_eq_primitive {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (hchi : chi ≠ 1) (t T : ℝ) :
    highZeroSum chi t T = highZeroSum chi.primitiveCharacter t T :=
  sum_highZeroIndices_eq_primitive chi hchi T (fun rho => (t : ℂ) ^ rho / rho)

end LiuWang.Proof.NonprincipalPsi
