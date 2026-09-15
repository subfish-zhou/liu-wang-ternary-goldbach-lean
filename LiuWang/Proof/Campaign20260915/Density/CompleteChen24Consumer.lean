import LiuWang.Proof.Campaign20260915.Density.CompleteChen24
import LiuWang.Proof.Campaign20260915.Density.CriticalPV
import LiuWang.Proof.SourceRoute.Density.Restart.ProductVertical

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_Qmean_chen24 (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    Qmean q ((q : ℝ) * y) (1 / 2) (y * u) ≤
      y * ((2.19021 * u + 2.906) * Real.log ((q : ℝ) * y) -
        (24 / Real.pi ^ 2) * Real.log q) := by
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  unfold Qmean
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  apply (div_le_iff₀ hphi).mpr
  exact (nonprincipal_Q_mean_chen24 q hy hu).trans_eq (by ring)

theorem source_familyMean_critical_chen24 (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    SourceRoute.Density.Restart.familyMean q ((q : ℝ) * y) (1 / 2) (y * u) ≤
      512 * Real.sqrt q * (1 + Real.log q) * (1 + y * u) *
        ((q.totient : ℝ) * y * ((2.19021 * u + 2.906) * Real.log ((q : ℝ) * y) -
          (24 / Real.pi ^ 2) * Real.log q)) + 4 * q * (y * u) := by
  have hy0 : 0 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hLq := Real.log_nonneg (Nat.one_le_cast.mpr (NeZero.pos q) : (1 : ℝ) ≤ q)
  have hQ := nonprincipal_Q_mean_chen24 q hy hu
  have h := (family_critical_le_Q_integrals q ((q : ℝ) * y) (mul_nonneg hy0 hu)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hQ
      (show 0 ≤ 512 * Real.sqrt q * (1 + Real.log q) * (1 + y * u) by positivity)) le_rfl)
  rw [SourceRoute.Density.Restart.familyMean]
  unfold SourceRoute.Density.Restart.familySquare
  rw [intervalIntegral.integral_finsetSum]
  · simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h
  · intro chi hc
    exact f_vertical_integrable
      ((NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc) _ _ _

#print axioms source_Qmean_chen24
#print axioms source_familyMean_critical_chen24

end LiuWang.Proof.Campaign20260915.Density
