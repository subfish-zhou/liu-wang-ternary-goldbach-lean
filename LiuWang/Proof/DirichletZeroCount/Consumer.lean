import LiuWang.Proof.DirichletZeroCount.Weighted

/-!
# Consumers on the actual psi high-real-part zero values

The old half-strip values occur only in these consumers, not in the producer's
definition of `N(alpha, chi, y)`. No pre-existing consumer or facade is changed.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.DirichletZeroCount

theorem half_nonprincipal_values_eq {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (y : ℝ) :
    zeroValues chi (1 / 2) y = NonprincipalPsi.highZeroValues chi y := by
  simp only [zeroValues, if_neg hchi, nonprincipalValues, nonprincipalIndices,
    NonprincipalPsi.highZeroValues, FixedHeightZeroSum.highZeroIndices]

theorem half_principal_values_eq (q : ℕ) [NeZero q] (y : ℝ) :
    zeroValues (1 : Character q) (1 / 2) y = PrincipalPsi.highZeroValues q y := by
  simp only [zeroValues, ↓reduceIte, principalValues, principalIndices,
    PrincipalPsi.highZeroValues, PrincipalPsi.highZeroIndices]

theorem nonprincipal_inverse_band_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1)
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ rho ∈ (NonprincipalPsi.highZeroValues chi y).filter (fun rho => u ≤ |rho.im|),
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) ≤ sharpenedBound chi y a / u := by
  simpa only [bandValues, half_nonprincipal_values_eq hchi] using
    band_inverse_sum_le chi (1 / 2) hu hy ha

theorem nonprincipal_inverse_sqrt_band_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1)
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ rho ∈ (NonprincipalPsi.highZeroValues chi y).filter (fun rho => u ≤ |rho.im|),
      (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) ≤
        sharpenedBound chi y a / Real.sqrt u := by
  simpa only [bandValues, half_nonprincipal_values_eq hchi] using
    band_inverse_sqrt_sum_le chi (1 / 2) hu hy ha

theorem principal_inverse_band_le (q : ℕ) [NeZero q]
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ rho ∈ (PrincipalPsi.highZeroValues q y).filter (fun rho => u ≤ |rho.im|),
      (analyticOrderNatAt (1 : Character q).LFunction rho : ℝ) / |rho.im|) ≤
        sharpenedBound (1 : Character q) y a / u := by
  simpa only [bandValues, half_principal_values_eq] using
    band_inverse_sum_le (1 : Character q) (1 / 2) hu hy ha

theorem principal_inverse_sqrt_band_le (q : ℕ) [NeZero q]
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ rho ∈ (PrincipalPsi.highZeroValues q y).filter (fun rho => u ≤ |rho.im|),
      (analyticOrderNatAt (1 : Character q).LFunction rho : ℝ) / Real.sqrt |rho.im|) ≤
        sharpenedBound (1 : Character q) y a / Real.sqrt u := by
  simpa only [bandValues, half_principal_values_eq] using
    band_inverse_sqrt_sum_le (1 : Character q) (1 / 2) hu hy ha

end LiuWang.Proof.DirichletZeroCount
