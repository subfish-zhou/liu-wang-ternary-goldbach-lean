import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.LowZeros
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ZeroFiberCardinality

/-! # 非对称开高度窗的精确有限重数索引 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonSymmetricContour

def rectangleZeroIndices {q : Nat} [NeZero q] (chi : Character q)
    (Hplus Hminus : Real) : Finset (CompletedZeroIndex chi) := by
  classical
  exact (criticalZeroIndices chi (|Hminus| + |Hplus| + 1)).filter
    (fun p => Hminus < (completedZeroValue p).im ∧ (completedZeroValue p).im < Hplus)

theorem mem_rectangleZeroIndices {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (Hplus Hminus : Real) (p : CompletedZeroIndex chi) :
    p ∈ rectangleZeroIndices chi Hplus Hminus ↔
      Hminus < (completedZeroValue p).im ∧ (completedZeroValue p).im < Hplus := by
  classical
  rw [rectangleZeroIndices, Finset.mem_filter]
  refine and_iff_right_of_imp ?_
  intro hp
  apply mem_criticalStripZeroTruncation_iff.mpr
  have hr := completedZeroValue_re_mem_Ioo hchi hPrimitive p
  refine ⟨hr.1, hr.2, abs_lt.mpr ⟨?_, ?_⟩⟩
  · change -(|Hminus| + |Hplus| + 1) < (completedZeroValue p).im
    linarith [neg_abs_le Hminus, abs_nonneg Hplus]
  · change (completedZeroValue p).im < |Hminus| + |Hplus| + 1
    linarith [le_abs_self Hplus, abs_nonneg Hminus]

def rectangleZeroValues {q : Nat} [NeZero q] (chi : Character q)
    (Hplus Hminus : Real) : Finset Complex := by
  classical
  exact (rectangleZeroIndices chi Hplus Hminus).image completedZeroValue

theorem zero_not_mem_rectangleZeroValues {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (Hplus Hminus : Real) :
    (0 : Complex) ∉ rectangleZeroValues chi Hplus Hminus := by
  classical
  rintro h
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
  have hr := (completedZeroValue_re_mem_Ioo hchi hPrimitive p).1
  simp [hp] at hr

theorem rectangleZeroFiber_card {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Hplus Hminus : Real} {rho : Complex}
    (hrho : rho ∈ rectangleZeroValues chi Hplus Hminus) :
    ((rectangleZeroIndices chi Hplus Hminus).filter
      (fun p => completedZeroValue p = rho)).card = analyticOrderNatAt chi.LFunction rho := by
  classical
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  have hheight := (mem_rectangleZeroIndices hchi hPrimitive Hplus Hminus p).mp hp
  have hre : 0 < rho.re := hpv ▸ (completedZeroValue_re_mem_Ioo hchi hPrimitive p).1
  have hne : rho ≠ 0 := by intro h; simp [h] at hre
  have hf :
      (rectangleZeroIndices chi Hplus Hminus).filter (fun p => completedZeroValue p = rho) =
        Complex.Hadamard.divisorZeroIndex₀_fiberFinset (symmetricCompletedLFunction chi) rho := by
    ext r
    rw [Finset.mem_filter, mem_rectangleZeroIndices hchi hPrimitive,
      Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset]
    change ((Hminus < (completedZeroValue r).im ∧ (completedZeroValue r).im < Hplus) ∧
      completedZeroValue r = rho) ↔ completedZeroValue r = rho
    refine and_iff_right_of_imp ?_
    intro hv
    simpa [hv, hpv] using hheight
  rw [hf, Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (differentiable_symmetricCompletedLFunction hchi) hne,
    analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hchi hre]

theorem sum_rectangleZeroValues_multiplicity {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (Hplus Hminus : Real) (f : Complex → Complex) :
    ∑ rho ∈ rectangleZeroValues chi Hplus Hminus,
        (analyticOrderNatAt chi.LFunction rho : Complex) * f rho =
      ∑ p ∈ rectangleZeroIndices chi Hplus Hminus, f (completedZeroValue p) := by
  classical
  have hf : ∀ rho ∈ rectangleZeroValues chi Hplus Hminus,
      ∑ p ∈ (rectangleZeroIndices chi Hplus Hminus).filter
          (fun p => completedZeroValue p = rho), f (completedZeroValue p) =
        (analyticOrderNatAt chi.LFunction rho : Complex) * f rho := by
    intro rho hrho
    calc
      _ = ∑ _p ∈ (rectangleZeroIndices chi Hplus Hminus).filter
          (fun p => completedZeroValue p = rho), f rho := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      _ = _ := by simp [rectangleZeroFiber_card hchi hPrimitive hrho]
  calc
    _ = ∑ rho ∈ rectangleZeroValues chi Hplus Hminus,
        ∑ p ∈ (rectangleZeroIndices chi Hplus Hminus).filter
          (fun p => completedZeroValue p = rho), f (completedZeroValue p) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact (hf rho hrho).symm
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (fun p => f (completedZeroValue p))

end LiuWang.Proof.NonSymmetricContour
