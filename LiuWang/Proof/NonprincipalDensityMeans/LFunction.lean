import LiuWang.Proof.NonprincipalDensityMeans.Mollifier
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLPrefixBoundedHarmonicTail

/-!
# Actual nonprincipal L-function means from a paid finite truncation

The prefix producer applies to every nonprincipal character at its original
modulus. The truncation length M remains independent of the height y.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans

def partialL {q : ℕ} (chi : Character q) (M : ℕ) (s : ℂ) : ℂ :=
  dirichletPolynomial chi ((range M).erase 0) (fun _ => 1) s

def truncationError (q M : ℕ) (y : ℝ) : ℝ :=
  2 * q * (1 + y) / Real.sqrt M

def Lmean (q : ℕ) [NeZero q] (sigma y : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
    ‖chi.LFunction ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient

def nonprincipalRatio (q : ℕ) : ℝ := ((q.totient - 1 : ℕ) : ℝ) / q.totient

theorem nonprincipalRatio_nonneg (q : ℕ) : 0 ≤ nonprincipalRatio q :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem norm_add_sq_le (z w : ℂ) : ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

theorem partialL_eq_Abel_sum {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (M : ℕ) (s : ℂ) :
    partialL chi M s = ∑ k ∈ range M,
      DirichletLAbelWeightVariation.cpowWeight s k * chi k := by
  have hq1 : q ≠ 1 := by
    intro he
    subst q
    exact hchi (Subsingleton.elim _ _)
  have hzero : chi 0 = 0 := chi.map_zero' hq1
  have he : (∑ k ∈ (range M).erase 0,
      DirichletLAbelWeightVariation.cpowWeight s k * chi k) =
      ∑ k ∈ range M, DirichletLAbelWeightVariation.cpowWeight s k * chi k := by
    apply sum_subset (erase_subset _ _)
    intro n hn hn'
    have : n = 0 := by simpa only [mem_erase, hn, and_true, not_not] using hn'
    simp [this, hzero]
  rw [← he]
  unfold partialL dirichletPolynomial
  apply sum_congr rfl
  intro n _
  simp only [DirichletLAbelWeightVariation.cpowWeight, Complex.ofReal_natCast,
    Complex.cpow_neg, one_mul, div_eq_mul_inv, mul_comm]

theorem LFunction_truncation_critical {q M : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hM : 1 ≤ M) {y t : ℝ} (ht : |t| ≤ y) :
    ‖chi.LFunction ((1 / 2 : ℂ) + t * Complex.I) -
      partialL chi M ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ truncationError q M y := by
  have h := DirichletCharacter.norm_LFunction_sub_sum_le_of_prefix_bound chi hchi
    ((1 / 2 : ℂ) + t * Complex.I) (by norm_num)
    (q : ℝ) (DirichletLWeakStripDerivative.norm_sum_range_character_le_modulus chi hchi) hM
  rw [← partialL_eq_Abel_sum hchi] at h
  have hs : ‖(1 / 2 : ℂ) + t * Complex.I‖ ≤ 1 / 2 + y := by
    have hb := norm_add_le (1 / 2 : ℂ) ((t : ℂ) * Complex.I)
    norm_num only [norm_div, norm_one, Complex.norm_ofNat, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hb
    linarith
  have hp : (M : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt M)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg M), Real.sqrt_eq_rpow]
  have hr : ((1 / 2 : ℂ) + t * Complex.I).re = (1 / 2 : ℝ) := by simp
  rw [hr, hp] at h
  have hm := mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr (Real.sqrt_nonneg (M : ℝ)))
  have hh : (q : ℝ) * ((Real.sqrt M)⁻¹ +
      ‖(1 / 2 : ℂ) + t * Complex.I‖ / (1 / 2) * (Real.sqrt M)⁻¹) ≤
        truncationError q M y := by
    unfold truncationError
    have hh := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg q)
    norm_num only [div_eq_mul_inv, inv_div, inv_one, mul_one] at hh ⊢
    nlinarith only [hh]
  exact h.trans hh

theorem LFunction_vertical_integrable {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (sigma y : ℝ) :
    IntervalIntegrable (fun t =>
      ‖chi.LFunction ((sigma : ℂ) + t * Complex.I)‖ ^ 2) volume (-y) y := by
  have hv : Continuous (fun t : ℝ => (sigma : ℂ) + t * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact (((DirichletCharacter.differentiable_LFunction hchi).continuous.comp hv).norm.pow 2).intervalIntegrable _ _

theorem critical_unitCoefficient_energy (M : ℕ) :
    (∑ n ∈ (range M).erase 0, ‖verticalCoefficient (fun _ => 1) (1 / 2) n‖ ^ 2) =
      harmonicRange M := by
  have he : (∑ n ∈ (range M).erase 0, (n : ℝ)⁻¹) = harmonicRange M := by
    apply sum_subset (erase_subset _ _)
    intro n hn hn'
    have : n = 0 := by simpa only [mem_erase, hn, and_true, not_not] using hn'
    simp [this]
  rw [← he]
  apply sum_congr rfl
  intro n hn
  have hn0 := Nat.pos_of_ne_zero (mem_erase.mp hn).1
  rw [verticalCoefficient, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn0,
    Complex.ofReal_re, ← Real.sqrt_eq_rpow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simp

theorem partialL_mean_le (q : ℕ) [NeZero q] (M : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖partialL chi M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) / q.totient ≤
        meanFactor q M y * harmonicRange M := by
  have h := dirichlet_mean_le q (Subset.refl ((range M).erase 0)) (fun _ => 1) (1 / 2) hy
  have hE := unitEnergy_le q ((range M).erase 0) (verticalCoefficient (fun _ => 1) (1 / 2))
  rw [critical_unitCoefficient_energy] at hE
  have hp : 0 ≤ (∫ t in -y..y,
      ‖dirichletPolynomial (1 : Character q) ((range M).erase 0) (fun _ => 1)
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2) / q.totient :=
    div_nonneg (intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hb := (h.trans (sub_le_self _ hp)).trans
    (mul_le_mul_of_nonneg_left hE (meanFactor_nonneg q M hy))
  simpa only [partialL, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hb

def LMeanBound (q M : ℕ) (y : ℝ) : ℝ :=
  2 * meanFactor q M y * harmonicRange M +
    4 * y * truncationError q M y ^ 2 * nonprincipalRatio q

theorem Lmean_critical_le (q : ℕ) [NeZero q] {M : ℕ} (hM : 1 ≤ M)
    {y : ℝ} (hy : 0 ≤ y) : Lmean q (1 / 2) y ≤ LMeanBound q M y := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖chi.LFunction ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        2 * (∫ t in -y..y, ‖partialL chi M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) +
          4 * y * truncationError q M y ^ 2 := by
    have hP := dirichletPolynomial_integrable chi ((range M).erase 0)
      (fun _ hn => Nat.pos_of_ne_zero (mem_erase.mp hn).1) (fun _ => 1) (1 / 2) y
    have hI := LFunction_vertical_integrable hchi (1 / 2) y
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hP hI
    change IntervalIntegrable (fun t => ‖partialL chi M
      ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) volume (-y) y at hP
    have hR : IntervalIntegrable (fun t => 2 * ‖partialL chi M
        ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 + 2 * truncationError q M y ^ 2) volume (-y) y :=
      (hP.const_mul 2).add intervalIntegrable_const
    have hb := intervalIntegral.integral_mono_on (by linarith : -y ≤ y) hI hR
      (fun t ht => by
        have ht' : |t| ≤ y := abs_le.mpr ht
        have htail := pow_le_pow_left₀ (norm_nonneg _) (LFunction_truncation_critical hchi hM ht') 2
        have hadd := norm_add_sq_le
          (partialL chi M ((1 / 2 : ℂ) + t * Complex.I))
          (chi.LFunction ((1 / 2 : ℂ) + t * Complex.I) -
            partialL chi M ((1 / 2 : ℂ) + t * Complex.I))
        rw [add_sub_cancel] at hadd
        linarith)
    rw [intervalIntegral.integral_add (hP.const_mul 2) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hb
    simp only [smul_eq_mul] at hb
    convert hb using 1
    ring
  have hsum := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_nonprincipalCharacters] at hsum
  have hb := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg q.totient)
  have hP := mul_le_mul_of_nonneg_left (partialL_mean_le q M hy) (by norm_num : (0 : ℝ) ≤ 2)
  unfold Lmean LMeanBound nonprincipalRatio
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  calc
    _ ≤ _ := hb
    _ ≤ _ := by
      simp only [div_eq_mul_inv] at hP ⊢
      nlinarith only [hP]

@[simp] theorem Lmean_one (sigma y : ℝ) : Lmean 1 sigma y = 0 := by simp [Lmean]

@[simp] theorem Lmean_two (sigma y : ℝ) : Lmean 2 sigma y = 0 := by simp [Lmean]

end LiuWang.Proof.NonprincipalDensityMeans
