import LiuWang.Proof.Campaign20260915.RosserCount.RosserPhase
import LiuWang.Proof.DirichletZeroCount.Remainder.GammaUpper
import LiuWang.Proof.Campaign20260915.ZetaWinding.TrapezoidRemainder

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Filter MeasureTheory Finset
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.DirichletZeroCount.Remainder
open LiuWang.Proof.Campaign20260915.ZetaWinding

def phaseSlope (z : ℂ) (x : ℝ) : ℝ :=
  -z.im / ((z.re + x) ^ 2 + z.im ^ 2)

def phaseCurvature (z : ℂ) (x : ℝ) : ℝ :=
  2 * z.im * (z.re + x) / ((z.re + x) ^ 2 + z.im ^ 2) ^ 2

theorem phaseSlope_hasDerivAt {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (phaseSlope z) (phaseCurvature z x) x := by
  have hden : (z.re + x) ^ 2 + z.im ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg z.im, sq_pos_of_pos (add_pos_of_pos_of_nonneg hz hx)]
  have hd := (((hasDerivAt_id x).const_add z.re).pow 2).add_const (z.im ^ 2)
  convert! (hasDerivAt_const x (-z.im)).div hd hden using 1
  unfold phaseCurvature
  dsimp only [Pi.pow_apply, id_eq]
  ring

theorem phaseCurvature_nonneg {z : ℂ} (hz : 0 < z.re) (hy : 0 ≤ z.im)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ phaseCurvature z x := by
  unfold phaseCurvature
  positivity

theorem phaseCurvature_continuousOn {z : ℂ} (hz : 0 < z.re) :
    ContinuousOn (phaseCurvature z) (Set.Ici 0) := by
  intro x hx
  have hden : (z.re + x) ^ 2 + z.im ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg z.im, sq_pos_of_pos (add_pos_of_pos_of_nonneg hz hx)]
  have hden2 := pow_ne_zero 2 hden
  apply ContinuousAt.continuousWithinAt
  unfold phaseCurvature
  fun_prop

theorem logGammaSeq_stirling_im_error {z : ℂ} (hz : 0 < z.re) (hy : 0 ≤ z.im)
    (N : ℕ) :
    |(logGammaSeq z N).im - stirlingPhase z - phaseTail z N| ≤ z.im / (8 * normSq z) := by
  let f : ℝ → ℝ := fun x => (Complex.log (z + (x : ℂ))).im
  let F : ℝ → ℝ := fun x =>
    ((z + (x : ℂ)) * Complex.log (z + (x : ℂ)) - (z + (x : ℂ))).im
  have hf (x : ℝ) (hx : 0 ≤ x) : HasDerivAt f (phaseSlope z x) x :=
    phase_hasDerivAt (by simp only [add_re, ofReal_re]; exact add_pos_of_pos_of_nonneg hz hx)
  have hF (x : ℝ) (hx : 0 ≤ x) : HasDerivAt F (f x) x :=
    phase_primitive (by simp only [add_re, ofReal_re]; exact add_pos_of_pos_of_nonneg hz hx)
  have hq := trapezoid_sum_abs hf (fun x hx => phaseSlope_hasDerivAt hz hx)
    (phaseCurvature_continuousOn hz) (phaseCurvature_continuousOn hz)
    (fun x hx => (abs_of_nonneg (phaseCurvature_nonneg hz hy hx)).le)
    hF (fun x hx => phaseSlope_hasDerivAt hz hx) N
  have he : (logGammaSeq z N).im - stirlingPhase z - phaseTail z N =
      -((∑ n ∈ range N, f n) + (f N - f 0) / 2 - (F N - F 0)) := by
    simp only [logGammaSeq, stirlingPhase, phaseTail, f, F, sub_im, add_im, mul_im,
      ofReal_re, ofReal_im, natCast_im, mul_zero, zero_add,
      add_zero, ofReal_zero, ofReal_natCast, div_ofNat_im, one_im,
      Complex.im_sum, Finset.sum_range_succ, sub_zero, zero_div]
    norm_num only [add_re, sub_re, neg_re, div_ofNat_re, one_re, natCast_re]
    ring
  have hN : phaseSlope z N ≤ 0 := by
    unfold phaseSlope
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hy) (by positivity)
  have h0 : phaseSlope z 0 = -z.im / normSq z := by
    simp [phaseSlope, normSq_apply, pow_two]
  rw [he, abs_neg]
  refine hq.trans ?_
  rw [h0, neg_div]
  have he' : z.im / (8 * normSq z) = (z.im / normSq z) / 8 := by ring
  rw [he']
  linarith

theorem logGamma_stirling_im_error {z : ℂ} (hz : 0 < z.re) (hy : 0 ≤ z.im) :
    |(logGamma z).im - stirlingPhase z| ≤ z.im / (8 * normSq z) := by
  have ht := (((Complex.continuous_im.tendsto _).comp
    (logGamma_tendsto hz)).sub_const (stirlingPhase z)).sub (phaseTail_tendsto hz)
  have hb := le_of_tendsto ht.abs
    (Eventually.of_forall (logGammaSeq_stirling_im_error hz hy))
  simpa only [sub_zero] using hb

#print axioms phaseSlope_hasDerivAt
#print axioms phaseCurvature_nonneg
#print axioms phaseCurvature_continuousOn
#print axioms logGammaSeq_stirling_im_error
#print axioms logGamma_stirling_im_error

end LiuWang.Proof.Campaign20260915.RosserCount
