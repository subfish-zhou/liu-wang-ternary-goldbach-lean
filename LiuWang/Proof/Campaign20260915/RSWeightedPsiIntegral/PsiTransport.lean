import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.Correction
import LiuWang.Proof.Campaign20260915.Totient.RSIntegratedAll
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

def errorPrimitive (x : ℝ) : ℝ := x ^ 2 / 2 - rsPsiPrimitive 1 x

def spectralPrimitive (x : ℝ) : ℝ := (∑' p, rsZeroPrimitive 1 x p).re

def regularPrimitive (x : ℝ) : ℝ :=
  Real.log (2 * Real.pi) * x - (gammaCorrection x).re

def weightedPrimitive (a b : ℝ) (F : ℝ → ℝ) : ℝ :=
  F b * weight b - F a * weight a - ∫ y in a..b, F y * weightSlope y

theorem weight_contDiffOn : ContDiffOn ℝ 1 weight (Ioi 1) := by
  have hl : ContDiffOn ℝ 1 Real.log (Ioi 1) :=
    contDiffOn_id.log (fun x hx => ne_of_gt (lt_trans zero_lt_one hx))
  exact (contDiffOn_const.add hl).div
    ((contDiffOn_id.pow 2).mul (hl.pow 2)) (fun x hx =>
      mul_ne_zero (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hx)))
        (pow_ne_zero _ (Real.log_pos hx).ne'))

theorem weightedPrimitive_eq_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    {F f : ℝ → ℝ} (hF : AbsolutelyContinuousOnInterval F a b)
    (hd : ∀ᵐ y, y ∈ uIcc a b → HasDerivAt F (f y) y) :
    weightedPrimitive a b F = ∫ y in a..b, f y * weight y := by
  have hsub : uIcc a b ⊆ Ioi (1 : ℝ) := by
    rw [uIcc_of_le hab]
    exact fun _ hy => ha.trans_le hy.1
  have hw := (weight_contDiffOn.mono hsub).absolutelyContinuousOnInterval
  have h := hw.integral_mul_deriv_eq_deriv_mul hF
  have hleft : (∫ y in a..b, weight y * deriv F y) =
      ∫ y in a..b, f y * weight y := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with y hy hyab
    rw [(hy (uIoc_subset_uIcc hyab)).deriv, mul_comm]
  have hright : (∫ y in a..b, deriv weight y * F y) =
      ∫ y in a..b, F y * weightSlope y := by
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    rw [(weight_hasDerivAt (hsub hy)).deriv, mul_comm]
  rw [hleft, hright] at h
  dsimp [weightedPrimitive]
  linarith

theorem errorPrimitive_spectral {x : ℝ} (hx : 1 < x) :
    errorPrimitive x = spectralPrimitive x + regularPrimitive x +
      (1 / 2 - Real.log (2 * Real.pi) - spectralPrimitive 1) := by
  have h := congrArg Complex.re (rsPsiPrimitive_one_spectral hx)
  norm_num [pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re] at h
  dsimp [errorPrimitive, spectralPrimitive, regularPrimitive]
  nlinarith

theorem errorPrimitive_ac {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval errorPrimitive a b := by
  have hb0 : 0 ≤ b := le_trans (by linarith : 0 ≤ a) hab
  have hp := (Chebyshev.psi_mono.intervalIntegrable (a := 0) (b := b)
    ).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hsub : uIcc a b ⊆ uIcc 0 b := by
    rw [uIcc_of_le hab, uIcc_of_le hb0]
    exact fun _ hy => ⟨le_trans (by linarith : 0 ≤ a) hy.1, hy.2⟩
  have hmain : AbsolutelyContinuousOnInterval (fun x : ℝ => x ^ 2 / 2) a b :=
    (show ContDiffOn ℝ 1 (fun x : ℝ => x ^ 2 / 2) (uIcc a b) by fun_prop
      ).absolutelyContinuousOnInterval
  exact hmain.sub (hp.mono hsub)

theorem errorPrimitive_ae_hasDerivAt {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∀ᵐ y, y ∈ uIcc a b → HasDerivAt errorPrimitive (y - Chebyshev.psi y) y := by
  have hb0 : 0 ≤ b := le_trans (by linarith : 0 ≤ a) hab
  filter_upwards [(Chebyshev.psi_mono.intervalIntegrable (a := 0) (b := b)
    ).ae_hasDerivAt_integral] with y hy hyab
  have hy0b : y ∈ uIcc (0 : ℝ) b := by
    rw [uIcc_of_le hab] at hyab
    rw [uIcc_of_le hb0]
    exact ⟨le_trans (by linarith : 0 ≤ a) hyab.1, hyab.2⟩
  have hd : HasDerivAt (fun x : ℝ => x ^ 2 / 2) y y := by
    convert! ((hasDerivAt_id y).pow 2).div_const 2 using 1
    simp
  exact hd.sub (hy hy0b 0 (by simp))

theorem actual_weighted_error_compact {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ y in a..b, (y - Chebyshev.psi y) * weight y) =
      weightedPrimitive a b errorPrimitive :=
  (weightedPrimitive_eq_integral ha hab (errorPrimitive_ac ha hab)
    (errorPrimitive_ae_hasDerivAt ha hab)).symm

theorem regularPrimitive_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt regularPrimitive (Real.log (2 * Real.pi) - rsTrivialKernel x) x := by
  convert!
    ((hasDerivAt_id x).const_mul (Real.log (2 * Real.pi))).sub
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (rsGammaCorrection_deriv hx)) using 1
  simp

theorem regularPrimitive_continuousOn : ContinuousOn regularPrimitive (Ioi 1) :=
  fun _ hx => (regularPrimitive_hasDerivAt hx).continuousAt.continuousWithinAt

theorem regular_weighted_compact {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    weightedPrimitive a b regularPrimitive = ∫ y in a..b, signedCorrection y := by
  have hsub : uIcc a b ⊆ Ioi (1 : ℝ) := by
    rw [uIcc_of_le hab]
    exact fun _ hy => ha.trans_le hy.1
  have hreg : IntervalIntegrable (fun y => Real.log (2 * Real.pi) - rsTrivialKernel y)
      volume a b := intervalIntegrable_const.sub
        ((rsTrivialKernel_antitone.mono hsub).intervalIntegrable)
  have hw : IntervalIntegrable weightSlope volume a b :=
    (weightSlope_continuousOn.mono hsub).intervalIntegrable
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y hy => weight_hasDerivAt (hsub hy))
    (fun y hy => regularPrimitive_hasDerivAt (hsub hy)) hw hreg
  change (∫ y in a..b, weight y * (Real.log (2 * Real.pi) - rsTrivialKernel y)) = _ at h
  have he : (∫ y in a..b, weight y * (Real.log (2 * Real.pi) - rsTrivialKernel y)) =
      ∫ y in a..b, signedCorrection y := by
    apply intervalIntegral.integral_congr
    intro y _
    exact mul_comm _ _
  rw [he] at h
  dsimp [weightedPrimitive]
  rw [show (fun y => regularPrimitive y * weightSlope y) =
    (fun y => weightSlope y * regularPrimitive y) by ext; ring]
  linarith

theorem weightedPrimitive_add {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    {F G : ℝ → ℝ} (hF : IntervalIntegrable F volume a b)
    (hG : IntervalIntegrable G volume a b) :
    weightedPrimitive a b (fun y => F y + G y) =
      weightedPrimitive a b F + weightedPrimitive a b G := by
  have hsub : uIcc a b ⊆ Ioi (1 : ℝ) := by
    rw [uIcc_of_le hab]
    exact fun _ hy => ha.trans_le hy.1
  unfold weightedPrimitive
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add
    (hF.mul_continuousOn (weightSlope_continuousOn.mono hsub))
    (hG.mul_continuousOn (weightSlope_continuousOn.mono hsub))]
  ring

theorem weightedPrimitive_const {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (c : ℝ) :
    weightedPrimitive a b (fun _ => c) = 0 := by
  have h := weightedPrimitive_eq_integral ha hab
    (F := fun _ => c) (f := fun _ => 0)
    contDiffOn_const.absolutelyContinuousOnInterval
    (Filter.Eventually.of_forall (fun _ _ => hasDerivAt_const _ _))
  simpa only [zero_mul, intervalIntegral.integral_zero] using h

theorem actual_weighted_spectral_compact {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ y in a..b, (y - Chebyshev.psi y) * weight y) =
      weightedPrimitive a b spectralPrimitive + ∫ y in a..b, signedCorrection y := by
  have hsub : uIcc a b ⊆ Ioi (1 : ℝ) := by
    rw [uIcc_of_le hab]
    exact fun _ hy => ha.trans_le hy.1
  have hz : IntervalIntegrable spectralPrimitive volume a b := by
    have hc : ContinuousOn spectralPrimitive (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact Complex.continuous_re.comp_continuousOn
        (rsZeroSum_continuousOn_Icc (by omega : 1 ≤ 1) ha.le)
    exact hc.intervalIntegrable
  have hr : IntervalIntegrable regularPrimitive volume a b :=
    (regularPrimitive_continuousOn.mono hsub).intervalIntegrable
  rw [actual_weighted_error_compact ha hab]
  have he : weightedPrimitive a b errorPrimitive =
      weightedPrimitive a b (fun y => spectralPrimitive y + regularPrimitive y +
        (1 / 2 - Real.log (2 * Real.pi) - spectralPrimitive 1)) := by
    unfold weightedPrimitive
    rw [errorPrimitive_spectral (ha.trans_le hab), errorPrimitive_spectral ha]
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    rw [errorPrimitive_spectral (hsub hy)]
  rw [he, weightedPrimitive_add ha hab (hz.add hr) intervalIntegrable_const,
    weightedPrimitive_const ha hab, add_zero, weightedPrimitive_add ha hab hz hr,
    regular_weighted_compact ha hab]

#print axioms actual_weighted_error_compact
#print axioms actual_weighted_spectral_compact

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
