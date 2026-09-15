import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.TailSeries

/-! Finite detector means obtained from actual Mobius tails, with a proved dominated limit. -/

set_option autoImplicit false

noncomputable section

open Finset Complex MeasureTheory Filter Set
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

def detectorPartial (y σ : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  -riemannZeta ((σ : ℂ) + t * I) * tailPartial ⌈y⌉₊ k σ t

theorem detectorPartial_continuous {σ : ℝ} (hσ : 1 < σ) (y : ℝ) (k : ℕ) :
    Continuous (detectorPartial y σ k) := by
  have hz : Continuous (fun t : ℝ => riemannZeta ((σ : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hs : (σ : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * I) (g := riemannZeta)
      (differentiableAt_riemannZeta hs).continuousAt
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)
  exact hz.neg.mul (tailPartial_continuous _ _ _)

theorem detectorPartial_bound {σ : ℝ} (hσ : 1 < σ) (y : ℝ) (k : ℕ) (t : ℝ) :
    ‖detectorPartial y σ k t‖ ≤ (1 + 1 / (σ - 1)) ^ 2 := by
  have hz := norm_zeta_le (s := (σ : ℂ) + t * I) (by simpa using hσ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, zero_mul, sub_self, add_zero] at hz
  rw [detectorPartial, norm_mul, norm_neg, pow_two]
  exact mul_le_mul hz (tailPartial_bound hσ _ _ _) (norm_nonneg _) (by positivity)

theorem detectorPartial_tendsto {σ : ℝ} (hσ : 1 < σ) (y t : ℝ) :
    Tendsto (fun k : ℕ => detectorPartial y σ k t) atTop
      (𝓝 (f y ((σ : ℂ) + t * I))) := by
  rw [f_eq_moebius_tail (by simpa using hσ)]
  exact (tailPartial_tendsto hσ ⌈y⌉₊ t).const_mul _

theorem detectorPartial_mean {y σ : ℝ} (hy : 1 < y) (hσ : 1 < σ)
    (k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖detectorPartial y σ k t‖ ^ 2) ≤
      (1 + 1 / (σ - 1)) ^ 2 *
        (2 * T / ((⌈y⌉₊ : ℝ) - 1) +
          8 * (3 * (1 + 1 / (2 * σ - 2)) +
            (1 / (σ - 1)) * (1 + 1 / (σ - 1))) +
          8 * (1 + 1 / (σ - 1)) ^ 2) := by
  have hN : 2 ≤ ⌈y⌉₊ := by
    have : 1 < ⌈y⌉₊ := Nat.lt_ceil.mpr (by simpa using hy)
    omega
  have hterm (t : ℝ) :
      ‖detectorPartial y σ k t‖ ^ 2 ≤
        (1 + 1 / (σ - 1)) ^ 2 * ‖tailPartial ⌈y⌉₊ k σ t‖ ^ 2 := by
    have hz := norm_zeta_le (s := (σ : ℂ) + t * I) (by simpa using hσ)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, zero_mul, sub_self, add_zero] at hz
    rw [detectorPartial, norm_mul, norm_neg, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz 2) (sq_nonneg _)
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -T ≤ T)
    (((detectorPartial_continuous hσ y k).norm.pow 2).intervalIntegrable _ _)
    ((((tailPartial_continuous ⌈y⌉₊ k σ).norm.pow 2).const_mul
      ((1 + 1 / (σ - 1)) ^ 2)).intervalIntegrable _ _) (fun t _ => hterm t)
  rw [intervalIntegral.integral_const_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (tailPartial_mean hσ hN k hT) (sq_nonneg _))

theorem M_right_mother {y σ : ℝ} (hy : 1 < y) (hσ : 1 < σ) {T : ℝ} (hT : 0 ≤ T) :
    M y σ T ≤
      (1 + 1 / (σ - 1)) ^ 2 *
        (2 * T / ((⌈y⌉₊ : ℝ) - 1) +
          8 * (3 * (1 + 1 / (2 * σ - 2)) +
            (1 / (σ - 1)) * (1 + 1 / (σ - 1))) +
          8 * (1 + 1 / (σ - 1)) ^ 2) := by
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (-T) T))
    (F := fun k t => ‖detectorPartial y σ k t‖ ^ 2)
    (f := fun t => F y ((σ : ℂ) + t * I))
    (fun _ => (1 + 1 / (σ - 1)) ^ 4)
    (fun k => ((detectorPartial_continuous hσ y k).norm.pow 2).aestronglyMeasurable)
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top))
    (fun k => Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h := pow_le_pow_left₀ (norm_nonneg _) (detectorPartial_bound hσ y k t) 2
      simpa only [← pow_mul] using h))
    (Eventually.of_forall (fun t => (detectorPartial_tendsto hσ y t).norm.pow 2))
  have hbound (k : ℕ) := detectorPartial_mean hy hσ k hT
  simp only [intervalIntegral.integral_of_le (show -T ≤ T by linarith),
    ← integral_Icc_eq_integral_Ioc] at hbound
  have h := le_of_tendsto hlim (Eventually.of_forall hbound)
  rw [M, intervalIntegral.integral_of_le (show -T ≤ T by linarith),
    ← integral_Icc_eq_integral_Ioc]
  exact h

theorem moving_mean_budget {y : ℝ} (hy : 10000 ≤ y) :
    (1 + 1 / delta y) ^ 2 ≤ 3 * Real.log y ^ 2 ∧
    8 * (3 * (1 + 1 / (2 * (1 + delta y) - 2)) +
      (1 / delta y) * (1 + 1 / delta y)) +
      8 * (1 + 1 / delta y) ^ 2 ≤ 44 * Real.log y ^ 2 := by
  have hL := log_ge_nine hy
  have hd := delta_bounds hy
  have hi : 1 / delta y = 3 * Real.log y / 2 := by
    unfold delta
    field_simp
  have hi2 : 1 / (2 * (1 + delta y) - 2) = (3 / 4) * Real.log y := by
    rw [show 2 * (1 + delta y) - 2 = 2 * delta y by ring]
    have he : 1 / (2 * delta y) = (1 / 2) * (1 / delta y) := by ring
    rw [he, hi]; ring
  rw [hi, hi2]
  constructor <;> nlinarith [sq_nonneg (Real.log y - 9)]

theorem M_moving_sharp {y : ℝ} (hy : 10000 ≤ y) {T : ℝ} (hT : 0 ≤ T) :
    M y (1 + delta y) T ≤
      (6 * T / (y - 1)) * Real.log y ^ 2 + 132 * Real.log y ^ 4 := by
  have hd := delta_bounds hy
  have hm := M_right_mother (by linarith : 1 < y) (by linarith : 1 < 1 + delta y) hT
  have hb := moving_mean_budget hy
  have hN := Nat.le_ceil y
  have hfirst : 2 * T / ((⌈y⌉₊ : ℝ) - 1) ≤ 2 * T / (y - 1) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hnn : 0 ≤ 2 * T / ((⌈y⌉₊ : ℝ) - 1) +
      8 * (3 * (1 + 1 / (2 * (1 + delta y) - 2)) +
        (1 / delta y) * (1 + 1 / delta y)) + 8 * (1 + 1 / delta y) ^ 2 := by
    have hden : 0 < 2 * (1 + delta y) - 2 := by linarith
    have hδ := hd.1
    have hceil : 0 < (⌈y⌉₊ : ℝ) - 1 := by linarith
    positivity
  simp only [add_sub_cancel_left] at hm
  have hsum := add_le_add hfirst hb.2
  have hmul := mul_le_mul hb.1 hsum (by simpa only [← add_assoc] using hnn)
    (by positivity : 0 ≤ 3 * Real.log y ^ 2)
  have hh := hm.trans (by simpa only [← add_assoc] using hmul)
  have he : 3 * Real.log y ^ 2 * (2 * T / (y - 1) + 44 * Real.log y ^ 2) =
      (6 * T / (y - 1)) * Real.log y ^ 2 + 132 * Real.log y ^ 4 := by ring
  exact hh.trans_eq he

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
