import LiuWang.Proof.Campaign20260915.Density.ChenCount

set_option autoImplicit false
noncomputable section

open Finset Set
open LiuWang.Proof.Interfaces
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem strict_nonprincipal_chen_all (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1) :
    (strictNonprincipalCount q alpha y : ℝ) ≤ chenBound q alpha y := by
  by_cases hq : 3 ≤ q
  · exact strict_nonprincipal_chen q hq hy ha ha1
  have hpos : 0 ≤ chenBound q alpha y := by
    have hL0 : 0 < Real.log ((q : ℝ) * y) := by linarith [source_product_log_ge_eleven q hy]
    have he : chenBound q alpha y =
        (250359 / Real.log ((q : ℝ) * y) + 5700) * chenDensityScale q y alpha := by
      unfold chenBound chenDensityScale
      ring
    rw [he]
    exact mul_nonneg (by positivity) (source_density_scale_pos q hy alpha).le
  have hsmall : q = 1 ∨ q = 2 := by have := NeZero.ne q; omega
  rcases hsmall with rfl | rfl
  · simpa only [strictNonprincipalCount_one, Nat.cast_zero] using hpos
  · simpa only [strictNonprincipalCount_two, Nat.cast_zero] using hpos

theorem family_sourceSeven_paid (q : ℕ) [NeZero q] {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1) :
    (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y :=
  family_sourceSeven_with_principal_paid q hy ha ha1
    (fun _ beta hb => strict_nonprincipal_chen_all q (alpha := beta) hy hb.1 hb.2)

theorem source_T7 (q : ℕ) [NeZero q] :
    ∀ alpha y : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y :=
  fun _ _ ha ha1 hy => family_sourceSeven_paid q hy ha ha1

theorem complete_family_sourceSeven_paid (q : ℕ) [NeZero q] {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
        (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      16541 * (Real.log y) ^ (6 : ℕ) +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) *
          (Real.log ((q : ℝ) * y)) ^ (6 * alpha) :=
  complete_family_sourceSeven_with_principal_paid q hy ha ha1
    (fun _ beta hb => strict_nonprincipal_chen_all q (alpha := beta) hy hb.1 hb.2)

#print axioms strict_nonprincipal_chen_all
#print axioms source_T7
#print axioms complete_family_sourceSeven_paid

end LiuWang.Proof.Campaign20260915.Density
