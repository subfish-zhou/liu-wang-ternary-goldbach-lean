import LiuWang.Proof.GlobalZeroDensity.Detector
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
LWD p.285, Lemma 3.4: the displayed Schwarz inequality and its exact numerical
payment. The two zeta estimates from (3.36) and Chen (24), k=1, are explicit
upstream inputs, not a replacement mean-value hypothesis on the detector.
-/

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

private theorem continuous_zeta_critical :
    Continuous (fun t : ℝ => riemannZeta ((1 / 2 : ℂ) + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : (1 / 2 : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  exact (differentiableAt_riemannZeta hs).continuousAt.comp
    (f := fun t : ℝ => (1 / 2 : ℂ) + t * I) (by fun_prop)

private theorem continuous_Q_critical (y : ℝ) :
    Continuous (fun t : ℝ => Q y ((1 / 2 : ℂ) + t * I)) :=
  (differentiable_Q y).continuous.comp (by fun_prop)

theorem integral_mul_le_sqrt_means {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, f t * g t) ≤
      Real.sqrt (∫ t in a..b, f t ^ 2) *
        Real.sqrt (∫ t in a..b, g t ^ 2) := by
  have hfm : MemLp f 2 (volume.restrict (Ioc a b)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
      (((hf.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have hgm : MemLp g 2 (volume.restrict (Ioc a b)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr
      (((hg.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc a b)) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hfm) (by simpa using hgm)
  simpa only [intervalIntegral.integral_of_le hab, Real.rpow_two,
    ← Real.sqrt_eq_rpow] using h

theorem critical_mean_schwarz (y : ℝ) {v Z : ℝ} (hv : 0 ≤ v)
    (hZ : ∀ t ∈ Icc (-v) v,
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ Z) :
    M y (1 / 2) v ≤ 2 * v +
      Z * (∫ t in -v..v, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) +
      2 * Real.sqrt (∫ t in -v..v, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2) *
        Real.sqrt (∫ t in -v..v, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) := by
  let z (t : ℝ) := ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖
  let p (t : ℝ) := ‖Q y ((1 / 2 : ℂ) + t * I)‖
  have hz : Continuous z := continuous_zeta_critical.norm
  have hp : Continuous p := (continuous_Q_critical y).norm
  have hpoint : ∀ t ∈ Icc (-v) v,
      F y (((1 / 2 : ℝ) : ℂ) + t * I) ≤ 1 + Z * p t ^ 2 + 2 * (z t * p t) := by
    intro t ht
    have h := norm_sub_le (riemannZeta ((1 / 2 : ℂ) + t * I) *
      Q y ((1 / 2 : ℂ) + t * I)) 1
    rw [norm_mul, norm_one] at h
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    have hmul := mul_le_mul_of_nonneg_right (hZ t ht) (sq_nonneg (p t))
    change ‖riemannZeta _ * Q y _ - 1‖ ^ 2 ≤ _
    dsimp [z, p] at *
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    nlinarith only [hsq, hmul]
  have hi : IntervalIntegrable (fun t => 1 + Z * p t ^ 2 + 2 * (z t * p t))
      volume (-v) v := (by fun_prop : Continuous
        (fun t => 1 + Z * p t ^ 2 + 2 * (z t * p t))).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by linarith : -v ≤ v)
    (intervalIntegrable_F y v (by norm_num : (1 / 2 : ℝ) ≠ 1)) hi hpoint
  have hip : IntervalIntegrable (fun t => Z * p t ^ 2) volume (-v) v :=
    (by fun_prop : Continuous (fun t => Z * p t ^ 2)).intervalIntegrable _ _
  have hizp : IntervalIntegrable (fun t => 2 * (z t * p t)) volume (-v) v :=
    (by fun_prop : Continuous (fun t => 2 * (z t * p t))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add hip) hizp,
    intervalIntegral.integral_add intervalIntegrable_const hip,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  have hcs := integral_mul_le_sqrt_means hz hp (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) (by linarith : -v ≤ v)
  change M y (1 / 2) v ≤ _ at h
  simpa only [z, p] using (show M y (1 / 2) v ≤ 2 * v +
    Z * (∫ t in -v..v, p t ^ 2) +
      2 * Real.sqrt (∫ t in -v..v, z t ^ 2) *
        Real.sqrt (∫ t in -v..v, p t ^ 2) by
          simp only [smul_eq_mul] at h
          linarith)

theorem source_height_log_bounds {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    17800 ≤ y ∧ 9.75 ≤ Real.log y := by
  have hl6 : 1.78 ≤ Real.log 6 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hy' : 17800 ≤ y := by linarith
  have he : Real.exp 1 ≤ 2.72 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hpow := pow_le_pow_left₀ (Real.exp_pos 1).le he 10
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow
  have hquarter := Real.add_one_le_exp (1 / 4)
  have hprod : Real.exp 9.75 * Real.exp (1 / 4) = Real.exp 10 := by
    rw [← Real.exp_add]
    norm_num
  have hexp : Real.exp 9.75 ≤ y := by
    nlinarith [Real.exp_pos 9.75]
  exact ⟨hy', (Real.le_log_iff_exp_le (by linarith)).mpr hexp⟩

theorem lemma_3_4_scalar {A v : ℝ} (hA : 502000 ≤ A) (hv : 0 ≤ v) :
    2 * v + 12.5 * (2 + v) * A +
      2 * Real.sqrt (8 * (2 + v) ^ 2) * Real.sqrt A ≤
        12.508 * (2 + v) * A := by
  have hA0 : 0 ≤ A := by linarith
  have hs := Real.sq_sqrt hA0
  have ht := Real.sq_sqrt (show 0 ≤ 8 * (2 + v) ^ 2 by positivity)
  have ht0 := Real.sqrt_nonneg (8 * (2 + v) ^ 2)
  have hroot : Real.sqrt (8 * (2 + v) ^ 2) ≤ 2.829 * (2 + v) := by
    nlinarith
  have hlow : 708 ≤ Real.sqrt A := by
    nlinarith [Real.sqrt_nonneg A]
  have hcross : 2 + 5.658 * Real.sqrt A ≤ 0.008 * A := by
    nlinarith [sq_nonneg (Real.sqrt A - 708)]
  have hm := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg A)
  have hn := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 2 + v by linarith)
  nlinarith

theorem lemma_3_4_from_original_inputs {y u : ℝ}
    (hy : 10000 * Real.log 6 ≤ y) (hu : 0 ≤ u)
    (hzmax : ∀ t ∈ Icc (-(y * u)) (y * u),
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ 12.5 * (2 + y * u))
    (hzmean : (∫ t in -(y * u)..y * u,
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤ 8 * (2 + y * u) ^ 2)
    (hchen24 : (∫ t in -(y * u)..y * u,
      ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y) :
    M y (1 / 2) (y * u) ≤
      12.508 * y * (2 + y * u) * (2.19021 * u + 2.906) * Real.log y := by
  obtain ⟨hy', hl⟩ := source_height_log_bounds hy
  let A := y * (2.19021 * u + 2.906) * Real.log y
  have hA : 502000 ≤ A := by
    have hyl : 17800 * 9.75 ≤ y * Real.log y :=
      mul_le_mul hy' hl (by norm_num) (by linarith)
    have hm := mul_le_mul_of_nonneg_right hyl (by norm_num : (0 : ℝ) ≤ 2.906)
    have he := mul_nonneg (show 0 ≤ y * Real.log y by positivity)
      (show 0 ≤ 2.19021 * u by positivity)
    dsimp [A]
    nlinarith
  have hv : 0 ≤ y * u := mul_nonneg (by linarith) hu
  have h := critical_mean_schwarz y hv hzmax
  have hq := mul_le_mul_of_nonneg_left hchen24
    (show 0 ≤ 12.5 * (2 + y * u) by positivity)
  have hr := mul_le_mul (Real.sqrt_le_sqrt hzmean) (Real.sqrt_le_sqrt hchen24)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs := lemma_3_4_scalar hA hv
  dsimp [A] at hs
  nlinarith

theorem zeta_sq_of_3_36 (t : ℝ)
    (h336 : ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      Real.sqrt 2 * (2 + (1 / 2 + |t|)⁻¹) * Real.sqrt (1 / 2 + |t|)) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ 8 * (2 + |t|) := by
  let r := 1 / 2 + |t|
  have hr : 1 / 2 ≤ r := by dsimp [r]; linarith [abs_nonneg t]
  have hr0 : 0 < r := by linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h336 2
  have heq : (Real.sqrt 2 * (2 + r⁻¹) * Real.sqrt r) ^ 2 =
      8 * r + 8 + 2 / r := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hr0.le]
    field_simp
    ring
  change _ ≤ (Real.sqrt 2 * (2 + r⁻¹) * Real.sqrt r) ^ 2 at hsq
  rw [heq] at hsq
  have hi : 2 / r ≤ 4 := (div_le_iff₀ hr0).mpr (by linarith)
  dsimp [r] at hsq hi
  linarith

private theorem integral_abs_symmetric {v : ℝ} (hv : 0 ≤ v) :
    (∫ t in -v..v, |t|) = v ^ 2 := by
  have hn : (∫ t in -v..0, |t|) = ∫ t in -v..0, -t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith : -v ≤ 0)] at ht
    exact abs_of_nonpos ht.2
  have hp : (∫ t in (0 : ℝ)..v, |t|) = ∫ t in (0 : ℝ)..v, t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hv] at ht
    exact abs_of_nonneg ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable (-v) 0) (continuous_abs.intervalIntegrable 0 v),
    hn, hp, intervalIntegral.integral_neg, integral_id, integral_id]
  ring

theorem zeta_inputs_of_3_36 {v : ℝ} (hv : 0 ≤ v)
    (h336 : ∀ t : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      Real.sqrt 2 * (2 + (1 / 2 + |t|)⁻¹) * Real.sqrt (1 / 2 + |t|)) :
    (∀ t ∈ Icc (-v) v,
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ 12.5 * (2 + v)) ∧
    (∫ t in -v..v, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      8 * (2 + v) ^ 2 := by
  constructor
  · intro t ht
    have habs : |t| ≤ v := abs_le.mpr ht
    exact (zeta_sq_of_3_36 t (h336 t)).trans (by linarith)
  · have hz := (continuous_zeta_critical.norm.pow 2).intervalIntegrable
      (μ := volume) (-v) v
    have hb : Continuous (fun t : ℝ => 8 * (2 + |t|)) := by fun_prop
    have h := intervalIntegral.integral_mono_on (by linarith : -v ≤ v)
      hz (hb.intervalIntegrable _ _) (fun t _ => zeta_sq_of_3_36 t (h336 t))
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const (continuous_abs.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_abs_symmetric hv] at h
    simp only [smul_eq_mul, Pi.pow_apply] at h
    nlinarith

theorem lemma_3_4_from_3_36_and_chen24 {y u : ℝ}
    (hy : 10000 * Real.log 6 ≤ y) (hu : 0 ≤ u)
    (h336 : ∀ t : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      Real.sqrt 2 * (2 + (1 / 2 + |t|)⁻¹) * Real.sqrt (1 / 2 + |t|))
    (hchen24 : (∫ t in -(y * u)..y * u,
      ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y) :
    M y (1 / 2) (y * u) ≤
      12.508 * y * (2 + y * u) * (2.19021 * u + 2.906) * Real.log y := by
  have hy' := (source_height_log_bounds hy).1
  obtain ⟨hmax, hmean⟩ := zeta_inputs_of_3_36
    (v := y * u) (mul_nonneg (by linarith : 0 ≤ y) hu) h336
  exact lemma_3_4_from_original_inputs hy hu hmax hmean hchen24

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
