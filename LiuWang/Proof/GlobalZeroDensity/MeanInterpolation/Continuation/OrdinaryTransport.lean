import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ZetaDensity
import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues

set_option autoImplicit false

noncomputable section

open Complex Set
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem ordinary_principal_values_eq_rectangle (q : ℕ) [NeZero q]
    {α y : ℝ} (hα : 0 < α) (hα2 : α ≤ 2) (hy : 0 ≤ y) :
    zeroValues (1 : Character q) α y =
      (zeta_rectangle_zeros_finite ((α : ℂ) - y * I) ((2 : ℂ) + y * I)).toFinset := by
  ext s
  rw [mem_zeroValues, (zeta_rectangle_zeros_finite _ _).mem_toFinset]
  have hre : (((α : ℂ) - y * I)).re ≤ (((2 : ℂ) + y * I)).re := by simpa using hα2
  have him : (((α : ℂ) - y * I)).im ≤ (((2 : ℂ) + y * I)).im := by
    simpa using (show -y ≤ y by linarith)
  constructor
  · rintro ⟨hz, ⟨hs0, hs1, hsy⟩, hsa⟩
    have hsne : s ≠ 1 := by intro he; simp [he] at hs1
    refine ⟨(mem_Rect hre him s).mpr ?_, hsne,
      (PrincipalPsi.principal_zero_iff_zeta_zero hs0 hsne).mp hz⟩
    simpa using (show α ≤ s.re ∧ s.re ≤ 2 ∧ -y ≤ s.im ∧ s.im ≤ y from
      ⟨hsa, by linarith, abs_le.mp hsy⟩)
  · rintro ⟨hs, hsne, hz⟩
    have hsm : α ≤ s.re ∧ s.re ≤ 2 ∧ -y ≤ s.im ∧ s.im ≤ y := by
      simpa using (mem_Rect hre him s).mp hs
    have hs0 : 0 < s.re := hα.trans_le hsm.1
    have hstrip := PrincipalPsi.Quantitative.zeta_zero_strip (by linarith : -2 < s.re) hz
    exact ⟨(PrincipalPsi.principal_zero_iff_zeta_zero hs0 hsne).mpr hz,
      ⟨hstrip.1, hstrip.2, abs_le.mpr hsm.2.2⟩, hsm.1⟩

theorem ordinary_principal_order_eq_zeta (q : ℕ) [NeZero q]
    {α y : ℝ} {s : ℂ} (hs : s ∈ zeroValues (1 : Character q) α y) :
    analyticOrderNatAt (1 : Character q).LFunction s = analyticOrderNatAt riemannZeta s := by
  obtain ⟨_, ⟨hs0, hs1, _⟩, _⟩ := mem_zeroValues.mp hs
  have hsne : s ≠ 1 := by intro he; simp [he] at hs1
  exact PrincipalPsi.analyticOrderNatAt_principal_eq_zeta hs0 hsne

theorem ordinary_principal_count_eq_rectangle (q : ℕ) [NeZero q]
    {α y : ℝ} (hα : 0 < α) (hα2 : α ≤ 2) (hy : 0 ≤ y) :
    count (1 : Character q) α y =
      zetaDetectorRectangleCount ((α : ℂ) - y * I) ((2 : ℂ) + y * I) := by
  rw [count, zetaDetectorRectangleCount, ← ordinary_principal_values_eq_rectangle q hα hα2 hy]
  exact Finset.sum_congr rfl (fun _ hs => ordinary_principal_order_eq_zeta q hs)

theorem ordinary_principal_high_alpha_density (q : ℕ) [NeZero q]
    {y α : ℝ} (hy : 10000 ≤ y) (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    (count (1 : Character q) α y : ℝ) ≤
      (1861 * y ^ (4 * (1 - (α - delta y))) * Real.log y ^ (6 * (α - delta y) - 1) +
        16 * y / (y - 1) ^ 2 + 4 * Real.pi * (1 - (α - delta y)) +
        argumentMajorant y (2 - α + 3 * delta y / 2) (α - delta y)) /
        (2 * Real.pi * delta y) := by
  have hd := (delta_bounds hy).1
  rw [ordinary_principal_count_eq_rectangle q (by linarith) (by linarith) (by linarith)]
  exact actual_zeta_high_alpha_density hy hα hα1

theorem ordinary_complete_principal_density (q : ℕ) [NeZero q]
    {y α : ℝ} (hy : 10000 ≤ y) (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    (∑ s ∈ (CompleteExpansion.zeroValues (1 : Character q) y).filter
      (fun s => α ≤ s.re), (analyticOrderNatAt (1 : Character q).LFunction s : ℝ)) ≤
      (1861 * y ^ (4 * (1 - (α - delta y))) * Real.log y ^ (6 * (α - delta y) - 1) +
        16 * y / (y - 1) ^ 2 + 4 * Real.pi * (1 - (α - delta y)) +
        argumentMajorant y (2 - α + 3 * delta y / 2) (α - delta y)) /
        (2 * Real.pi * delta y) := by
  have hd := (delta_bounds hy).1
  simpa only [count, Applications.values_eq_complete_filter _
    (show 1 / 2 ≤ α by linarith), Nat.cast_sum] using
    ordinary_principal_high_alpha_density q hy hα hα1

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
