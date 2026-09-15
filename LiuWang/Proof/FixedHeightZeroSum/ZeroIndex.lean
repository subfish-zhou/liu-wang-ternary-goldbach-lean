import LiuWang.Proof.NonSymmetricContour.ZeroIndex

/-!
# 固定闭高度的保重数索引

先取严格的 `T + 1` 窗，再截到闭窗；不要求端点避开零点。
高实部包含临界线，低实部不包含临界线。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.FixedHeightZeroSum

def fixedZeroIndices {q : Nat} [NeZero q] (chi : Character q) (T : Real) :
    Finset (CompletedZeroIndex chi) := by
  classical
  exact (criticalZeroIndices chi (T + 1)).filter
    (fun p => |(completedZeroValue p).im| ≤ T)

theorem mem_fixedZeroIndices {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) (p : CompletedZeroIndex chi) :
    p ∈ fixedZeroIndices chi T ↔ |(completedZeroValue p).im| ≤ T := by
  classical
  rw [fixedZeroIndices, Finset.mem_filter]
  refine and_iff_right_of_imp ?_
  intro hp
  apply mem_criticalStripZeroTruncation_iff.mpr
  have hr := completedZeroValue_re_mem_Ioo hchi hPrimitive p
  refine ⟨hr.1, hr.2, ?_⟩
  change |(completedZeroValue p).im| < T + 1
  linarith

def highZeroIndices {q : Nat} [NeZero q] (chi : Character q) (T : Real) :
    Finset (CompletedZeroIndex chi) := by
  classical
  exact (fixedZeroIndices chi T).filter (fun p => 1 / 2 ≤ (completedZeroValue p).re)

def lowZeroIndices {q : Nat} [NeZero q] (chi : Character q) (T : Real) :
    Finset (CompletedZeroIndex chi) := by
  classical
  exact (fixedZeroIndices chi T).filter (fun p => (completedZeroValue p).re < 1 / 2)

theorem mem_highZeroIndices {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) (p : CompletedZeroIndex chi) :
    p ∈ highZeroIndices chi T ↔
      |(completedZeroValue p).im| ≤ T ∧ 1 / 2 ≤ (completedZeroValue p).re := by
  classical
  simp only [highZeroIndices, Finset.mem_filter, mem_fixedZeroIndices hchi hPrimitive]

theorem mem_lowZeroIndices {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) (p : CompletedZeroIndex chi) :
    p ∈ lowZeroIndices chi T ↔
      |(completedZeroValue p).im| ≤ T ∧ (completedZeroValue p).re < 1 / 2 := by
  classical
  simp only [lowZeroIndices, Finset.mem_filter, mem_fixedZeroIndices hchi hPrimitive]

theorem lowZeroIndices_eq {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (T : Real) :
    lowZeroIndices chi T =
      LocalAnalyticBounds.LeftVertical.lowZeroFinset hchi hPrimitive T := by
  classical
  ext p
  rw [mem_lowZeroIndices hchi hPrimitive,
    LocalAnalyticBounds.LeftVertical.mem_lowZeroFinset]
  have hr := (completedZeroValue_re_mem_Ioo hchi hPrimitive p).1
  change (_ ∧ _) ↔ ((_ ∧ _) ∧ _)
  tauto

theorem sum_fixed_eq_low_add_high {q : Nat} [NeZero q] (chi : Character q)
    (T : Real) (f : CompletedZeroIndex chi → Complex) :
    ∑ p ∈ fixedZeroIndices chi T, f p =
      (∑ p ∈ lowZeroIndices chi T, f p) + ∑ p ∈ highZeroIndices chi T, f p := by
  classical
  simpa only [lowZeroIndices, highZeroIndices, not_lt] using
    (Finset.sum_filter_add_sum_filter_not (fixedZeroIndices chi T)
      (fun p => (completedZeroValue p).re < 1 / 2) f).symm

def fixedZeroValues {q : Nat} [NeZero q] (chi : Character q) (T : Real) :
    Finset Complex := by
  classical
  exact (fixedZeroIndices chi T).image completedZeroValue

theorem fixedZeroFiber_card {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} {rho : Complex} (hrho : rho ∈ fixedZeroValues chi T) :
    ((fixedZeroIndices chi T).filter (fun p => completedZeroValue p = rho)).card =
      analyticOrderNatAt chi.LFunction rho := by
  classical
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  have hheight := (mem_fixedZeroIndices hchi hPrimitive T p).mp hp
  have hre : 0 < rho.re := hpv ▸ (completedZeroValue_re_mem_Ioo hchi hPrimitive p).1
  have hne : rho ≠ 0 := by intro h; simp [h] at hre
  have hf :
      (fixedZeroIndices chi T).filter (fun p => completedZeroValue p = rho) =
        Complex.Hadamard.divisorZeroIndex₀_fiberFinset (symmetricCompletedLFunction chi) rho := by
    ext r
    rw [Finset.mem_filter, mem_fixedZeroIndices hchi hPrimitive,
      Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset]
    change (_ ∧ completedZeroValue r = rho) ↔ completedZeroValue r = rho
    refine and_iff_right_of_imp ?_
    intro hv
    simpa [hv, hpv] using hheight
  rw [hf, Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (differentiable_symmetricCompletedLFunction hchi) hne,
    analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hchi hre]

theorem sum_fixedZeroValues_multiplicity {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) (f : Complex → Complex) :
    ∑ rho ∈ fixedZeroValues chi T,
        (analyticOrderNatAt chi.LFunction rho : Complex) * f rho =
      ∑ p ∈ fixedZeroIndices chi T, f (completedZeroValue p) := by
  classical
  have hf : ∀ rho ∈ fixedZeroValues chi T,
      ∑ p ∈ (fixedZeroIndices chi T).filter (fun p => completedZeroValue p = rho),
          f (completedZeroValue p) =
        (analyticOrderNatAt chi.LFunction rho : Complex) * f rho := by
    intro rho hrho
    calc
      _ = ∑ _p ∈ (fixedZeroIndices chi T).filter
          (fun p => completedZeroValue p = rho), f rho := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      _ = _ := by simp [fixedZeroFiber_card hchi hPrimitive hrho]
  calc
    _ = ∑ rho ∈ fixedZeroValues chi T,
        ∑ p ∈ (fixedZeroIndices chi T).filter (fun p => completedZeroValue p = rho),
          f (completedZeroValue p) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact (hf rho hrho).symm
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (fun p => f (completedZeroValue p))

end LiuWang.Proof.FixedHeightZeroSum
