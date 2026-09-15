import LiuWang.Proof.Campaign20260915.Density.CriticalPV
import LiuWang.Proof.Campaign20260915.Density.FamilyWeightedRight

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.GlobalZeroDensity.Sharp (ceil_log_bounds)
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem Qmean_source_critical (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : 10000 ≤ y) (hu : 0 ≤ u) :
    Qmean q ((q : ℝ) * y) (1 / 2) (y * u) ≤
      y * (2 * u + 4.1 * (1.01 + Real.log y)) * (1.01 + Real.log ((q : ℝ) * y)) := by
  let X : ℝ := (q : ℝ) * y
  let N : ℕ := ⌈X⌉₊
  let K : ℕ := N / q + 1
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hy0 : 0 < y := by linarith
  have hyX : y ≤ X := by dsimp [X]; nlinarith
  obtain ⟨hN, hlogN⟩ := ceil_log_bounds (hy.trans hyX)
  have hNX : (N : ℝ) / q ≤ 1.001 * y := by
    apply (div_le_iff₀ hq0).mpr
    dsimp [N, X] at hN ⊢
    nlinarith only [hN]
  have hK : (K : ℝ) ≤ 1.01 * y := by
    have hd : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
    dsimp [K]
    push_cast
    linarith
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.mpr (Nat.succ_pos (N / q))
  have hlogK : Real.log K ≤ Real.log y + 0.01 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hK0 hy0)
    rw [Real.log_div hK0.ne' hy0.ne'] at h
    have hd : (K : ℝ) / y ≤ 1.01 := (div_le_iff₀ hy0).mpr hK
    linarith
  have hLy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hKN : 0 ≤ 1 + Real.log K := by
    have h := Real.log_nonneg (Nat.one_le_cast.mpr (Nat.succ_pos (N / q)))
    linarith
  have hNN : 0 ≤ 1 + Real.log N := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ N by
      have := Nat.le_ceil X
      dsimp [N]
      linarith)
    linarith
  have hprod := mul_le_mul hNX
    (show 1 + Real.log K ≤ 1.01 + Real.log y by linarith) hKN
    (show 0 ≤ 1.001 * y by positivity)
  have hfirst : 2 * (y * u) + 4 * (N : ℝ) / q * (1 + Real.log K) ≤
      y * (2 * u + 4.1 * (1.01 + Real.log y)) := by
    have hn := mul_nonneg hy0.le (show 0 ≤ 1.01 + Real.log y by positivity)
    simp only [div_eq_mul_inv] at hprod ⊢
    nlinarith only [hprod, hn]
  have h := mul_le_mul hfirst
    (show 1 + Real.log N ≤ 1.01 + Real.log X by dsimp [N]; linarith)
    hNN (by positivity)
  exact (Qmean_critical_log_bound q X (mul_nonneg hy0.le hu)).trans h

def criticalWindowBudget (q : ℕ) (y u : ℝ) : ℝ :=
  512 * q * Real.sqrt q * y ^ 2 * (1 + Real.log q) * (1.01 + Real.log ((q : ℝ) * y)) *
    ((u + 0.0001) * (2 * u + 4.1 * (1.01 + Real.log y))) + 4 * q * y * u

theorem source_family_critical_window (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    SourceRoute.Density.Restart.familyMean q ((q : ℝ) * y) (1 / 2) (y * u) ≤
      criticalWindowBudget q y u := by
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hy0 : 0 < y := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hLq := Real.log_nonneg hq
  have hLy := Real.log_nonneg (show 1 ≤ y by linarith)
  have hLX := Real.log_nonneg (show 1 ≤ (q : ℝ) * y by nlinarith)
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hQ := Qmean_source_critical q hy' hu
  unfold Qmean at hQ
  have hQ' := (div_le_iff₀ hphi).mp hQ
  have hp : (q.totient : ℝ) ≤ q := Nat.cast_le.mpr (Nat.totient_le q)
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤
    y * (2 * u + 4.1 * (1.01 + Real.log y)) * (1.01 + Real.log ((q : ℝ) * y)) by positivity)
  have hQ'' := hQ'.trans hp'
  have h := family_critical_le_Q_integrals q ((q : ℝ) * y) (mul_nonneg hy0.le hu)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hQ''
  have hmean := mul_le_mul_of_nonneg_left hQ'' (show 0 ≤
    512 * Real.sqrt q * (1 + Real.log q) * (1 + y * u) by positivity)
  have htime : 1 + y * u ≤ y * (u + 0.0001) := by nlinarith
  have ht := mul_le_mul_of_nonneg_left htime (show 0 ≤
    512 * Real.sqrt q * (1 + Real.log q) *
      (y * (2 * u + 4.1 * (1.01 + Real.log y)) *
        (1.01 + Real.log ((q : ℝ) * y)) * q) by positivity)
  rw [SourceRoute.Density.Restart.familyMean]
  unfold SourceRoute.Density.Restart.familySquare
  rw [intervalIntegral.integral_finsetSum]
  · norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    unfold criticalWindowBudget
    nlinarith only [h, hmean, ht]
  · intro chi hc
    exact f_vertical_integrable
      ((NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc) _ _ _

#print axioms source_family_critical_window

end LiuWang.Proof.Campaign20260915.Density
