import LiuWang.Proof.Campaign20260915.Density.OrdinaryCritical
import LiuWang.Proof.Campaign20260915.Density.FamilyWeightedRight

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

namespace LiuWang.Proof.Campaign20260915.Density

def sharpCriticalPolynomial (a L u : ℝ) : ℝ :=
  (u + 0.0002) * ((2.19021 * u + 2.906) * L - 2.4 * a)

theorem chen24_rounded_bracket_nonneg {a L u : ℝ}
    (hL : 0 ≤ L) (haL : a ≤ L) (hu : 0 ≤ u) :
    0 ≤ (2.19021 * u + 2.906) * L - 2.4 * a := by
  nlinarith [mul_nonneg hu hL]

def sharpCriticalWindowBudget (q : ℕ) (y u : ℝ) : ℝ :=
  16.016 * q * Real.sqrt q * y ^ 2 * Real.log q *
    sharpCriticalPolynomial (Real.log q) (Real.log ((q : ℝ) * y)) u + 2002 * q * y * u

theorem source_family_critical_sharp_window (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    SourceRoute.Density.Restart.familyMean q ((q : ℝ) * y) (1 / 2) (y * u) ≤
      sharpCriticalWindowBudget q y u := by
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hy0 : 0 < y := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hLq := Real.log_nonneg (Nat.one_le_cast.mpr (NeZero.pos q) : (1 : ℝ) ≤ q)
  have hLy := Real.log_nonneg (show 1 ≤ y by linarith)
  have hlog := Real.log_mul hq0.ne' hy0.ne'
  have hL := source_product_log_ge_eleven q hy
  have haL : Real.log q ≤ Real.log ((q : ℝ) * y) := by rw [hlog]; linarith
  let R : ℝ := (2.19021 * u + 2.906) * Real.log ((q : ℝ) * y) - 2.4 * Real.log q
  have hR : 0 ≤ R := chen24_rounded_bracket_nonneg (by linarith) haL hu
  have hc : 2.4 ≤ 24 / Real.pi ^ 2 := by
    calc
      _ = 4 * (0.6 : ℝ) := by norm_num
      _ ≤ 4 * (6 / Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left euler_density_bounds.1 (by norm_num)
      _ = _ := by ring
  have hc' := mul_le_mul_of_nonneg_right hc hLq
  have hQB := mul_le_mul_of_nonneg_left
    (show (2.19021 * u + 2.906) * Real.log ((q : ℝ) * y) -
        (24 / Real.pi ^ 2) * Real.log q ≤ R by dsimp [R]; linarith)
    (show 0 ≤ (q.totient : ℝ) * y by positivity)
  have hQ := (nonprincipal_Q_mean_chen24 q hy hu).trans hQB
  let C : ℝ := 16.016 * ((q : ℝ) * Real.sqrt q * Real.log q / q.totient) * (2 + y * u)
  have hm := mul_le_mul_of_nonneg_left hQ (show 0 ≤ C by dsimp [C]; positivity)
  have he : C * ((q.totient : ℝ) * y * R) =
      16.016 * q * Real.sqrt q * Real.log q * (2 + y * u) * y * R := by
    dsimp [C]
    field_simp
  rw [he] at hm
  have htime : 2 + y * u ≤ y * (u + 0.0002) := by nlinarith
  have ht := mul_le_mul_of_nonneg_left htime
    (show 0 ≤ 16.016 * q * Real.sqrt q * Real.log q * y * R by positivity)
  have h := family_critical_sharp_Q q ((q : ℝ) * y) (mul_nonneg hy0.le hu)
  change _ ≤ C * _ + _ at h
  rw [SourceRoute.Density.Restart.familyMean]
  unfold SourceRoute.Density.Restart.familySquare
  rw [intervalIntegral.integral_finsetSum]
  · simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    unfold sharpCriticalWindowBudget sharpCriticalPolynomial
    dsimp [R] at hm ht
    nlinarith only [h, hm, ht]
  · intro chi hc
    exact f_vertical_integrable ((mem_nonprincipalCharacters chi).mp hc) _ _ _

#print axioms source_family_critical_sharp_window

end LiuWang.Proof.Campaign20260915.Density
