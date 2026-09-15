import LiuWang.Proof.Campaign20260915.ZetaValidation.GammaPhaseTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Finset

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def logPhase (z : ℂ) (u : ℝ) : ℝ := (log (z + u)).im

def logPhaseSlope (z : ℂ) (u : ℝ) : ℝ := ((z + u)⁻¹).im

def logPhaseCurvature (z : ℂ) (u : ℝ) : ℝ :=
  2 * z.im * (z.re + u) / ((z.re + u) ^ 2 + z.im ^ 2) ^ 2

def logPhasePrimitive (z : ℂ) (u : ℝ) : ℝ :=
  ((z + u) * log (z + u) - (z + u)).im

theorem logPhase_derivative {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (logPhase z) (logPhaseSlope z u) u := by
  have hd : HasDerivAt (fun u : ℝ => z + (u : ℂ)) 1 u := by
    simpa using (ofRealCLM.hasDerivAt (x := u)).const_add z
  have hl := hd.clog_real (mem_slitPlane_iff.mpr (Or.inl (by simp; linarith)))
  simpa only [logPhase, logPhaseSlope, one_div, imCLM_apply] using!
    imCLM.hasFDerivAt.comp_hasDerivAt u hl

theorem logPhaseSlope_derivative {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (logPhaseSlope z) (logPhaseCurvature z u) u := by
  have hd : HasDerivAt (fun u : ℝ => z + (u : ℂ)) 1 u := by
    simpa using (ofRealCLM.hasDerivAt (x := u)).const_add z
  have hn : z + (u : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, zero_re] at this
    linarith
  have h := imCLM.hasFDerivAt.comp_hasDerivAt u (hd.inv hn)
  have he : (-1 / (z + (u : ℂ)) ^ 2).im = logPhaseCurvature z u := by
    rw [div_eq_mul_inv, ← inv_pow]
    simp [logPhaseCurvature, pow_two, mul_im, inv_re, inv_im, normSq_apply]
    field_simp
    ring
  change HasDerivAt (logPhaseSlope z) (-1 / (z + (u : ℂ)) ^ 2).im u at h
  rw [he] at h
  exact h

theorem logPhasePrimitive_derivative {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (logPhasePrimitive z) (logPhase z u) u := by
  have hd : HasDerivAt (fun u : ℝ => z + (u : ℂ)) 1 u := by
    simpa using (ofRealCLM.hasDerivAt (x := u)).const_add z
  have hn : z + (u : ℂ) ≠ 0 :=
    ne_zero_of_re_pos (by simp; linarith)
  have hl := hd.clog_real (mem_slitPlane_iff.mpr (Or.inl (by simp; linarith)))
  have h := imCLM.hasFDerivAt.comp_hasDerivAt u ((hd.mul hl).sub hd)
  simpa only [logPhasePrimitive, logPhase, one_mul, one_div, mul_inv_cancel₀ hn,
    add_sub_cancel_right, imCLM_apply] using! h

private theorem trapezoid_unit_bound {f g h : ℝ → ℝ} {a : ℝ}
    (hf : ∀ u ∈ Set.uIcc a (a + 1), HasDerivAt f (g u) u)
    (hg : ∀ u ∈ Set.uIcc a (a + 1), HasDerivAt g (h u) u)
    (hi : ContinuousOn h (Set.uIcc a (a + 1)))
    (hpos : ∀ u ∈ Set.Icc a (a + 1), 0 ≤ h u) :
    0 ≤ (f a + f (a + 1)) / 2 - ∫ u in a..a + 1, f u ∧
      (f a + f (a + 1)) / 2 - (∫ u in a..a + 1, f u) ≤
        (g (a + 1) - g a) / 8 := by
  let p : ℝ → ℝ := fun u => (u - a) * (u - a - 1) / 2
  let d : ℝ → ℝ := fun u => u - a - 1 / 2
  have hp : ∀ u ∈ Set.uIcc a (a + 1), HasDerivAt p (d u) u := by
    intro u _
    convert! (((hasDerivAt_id u).sub_const a).mul
      (((hasDerivAt_id u).sub_const a).sub_const 1)).div_const 2 using 1
    dsimp [d]
    ring
  have hd : ∀ u ∈ Set.uIcc a (a + 1), HasDerivAt d 1 u := by
    intro u _
    simpa only [d] using! ((hasDerivAt_id u).sub_const a).sub_const (1 / 2)
  have hgi : IntervalIntegrable g volume a (a + 1) :=
    (continuousOn_of_forall_continuousAt (fun u hu => (hg u hu).continuousAt)).intervalIntegrable
  have hfi : IntervalIntegrable f volume a (a + 1) :=
    (continuousOn_of_forall_continuousAt (fun u hu => (hf u hu).continuousAt)).intervalIntegrable
  have hdi : IntervalIntegrable d volume a (a + 1) :=
    (by fun_prop : Continuous d).intervalIntegrable _ _
  have hpi : IntervalIntegrable p volume a (a + 1) :=
    (by fun_prop : Continuous p).intervalIntegrable _ _
  have he1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hd hgi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a (a + 1))
  have he2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg hp hi.intervalIntegrable hdi
  have he : (f a + f (a + 1)) / 2 - (∫ u in a..a + 1, f u) =
      ∫ u in a..a + 1, -p u * h u := by
    simp only [mul_one] at he1
    have hp0 : p a = 0 := by simp [p]
    have hp1 : p (a + 1) = 0 := by simp [p]
    have hd0 : d a = -1 / 2 := by dsimp [d]; ring
    have hd1 : d (a + 1) = 1 / 2 := by dsimp [d]; ring
    rw [hp0, hp1, mul_zero, mul_zero, sub_self] at he2
    rw [hd0, hd1] at he1
    have hx : (∫ u in a..a + 1, -p u * h u) =
        -(∫ u in a..a + 1, h u * p u) := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext u
      ring
    rw [hx]
    linarith
  have hb (u : ℝ) (hu : u ∈ Set.Icc a (a + 1)) : 0 ≤ -p u ∧ -p u ≤ 1 / 8 := by
    dsimp [p]
    constructor
    · have := mul_nonpos_of_nonneg_of_nonpos (by linarith [hu.1] : 0 ≤ u - a)
        (by linarith [hu.2] : u - a - 1 ≤ 0)
      linarith
    · nlinarith [sq_nonneg (u - a - 1 / 2)]
  rw [he]
  constructor
  · exact intervalIntegral.integral_nonneg (by linarith)
      (fun u hu => mul_nonneg (hb u hu).1 (hpos u hu))
  · calc
      _ ≤ ∫ u in a..a + 1, (1 / 8 : ℝ) * h u :=
        intervalIntegral.integral_mono_on (by linarith)
          (hpi.neg.mul_continuousOn hi) (hi.intervalIntegrable.const_mul _)
          (fun u hu => mul_le_mul_of_nonneg_right (hb u hu).2 (hpos u hu))
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_eq_sub_of_hasDerivAt hg hi.intervalIntegrable]
        ring

def gammaTrapezoidError (z : ℂ) (N : ℕ) : ℝ :=
  (∑ n ∈ range (N + 1), logPhase z n) -
    (logPhase z 0 + logPhase z N) / 2 -
      (logPhasePrimitive z N - logPhasePrimitive z 0)

theorem gammaTrapezoidError_bound {z : ℂ} (hz : 0 < z.re) (ht : 0 ≤ z.im) (N : ℕ) :
    0 ≤ gammaTrapezoidError z N ∧
      gammaTrapezoidError z N ≤ (logPhaseSlope z N - logPhaseSlope z 0) / 8 := by
  have hi {n : ℕ} : ContinuousOn (logPhaseCurvature z) (Set.uIcc (n : ℝ) (n + 1)) := by
    rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ n + 1)]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hp : 0 < (z.re + u) ^ 2 + z.im ^ 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : 0 < z.re + u := by linarith [hu.1]
      positivity
    exact pow_ne_zero _ hp.ne'
  have hu {n : ℕ} {u : ℝ} (hu : u ∈ Set.uIcc (n : ℝ) (n + 1)) : 0 ≤ u := by
    rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ n + 1)] at hu
    exact (Nat.cast_nonneg n).trans hu.1
  induction N with
  | zero => simp [gammaTrapezoidError]
  | succ N ih =>
    have hunit := trapezoid_unit_bound (a := (N : ℝ))
      (fun u hu' => logPhase_derivative hz (hu hu'))
      (fun u hu' => logPhaseSlope_derivative hz (hu hu')) hi
      (fun u hu' => show 0 ≤ logPhaseCurvature z u from by
        dsimp [logPhaseCurvature]
        have : 0 ≤ u := (Nat.cast_nonneg N).trans hu'.1
        positivity)
    have hfi : IntervalIntegrable (logPhase z) volume (N : ℝ) (N + 1) :=
      (continuousOn_of_forall_continuousAt
        (fun u hu' => (logPhase_derivative hz (hu hu')).continuousAt)).intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu' => logPhasePrimitive_derivative hz (hu hu')) hfi] at hunit
    have he : gammaTrapezoidError z (N + 1) = gammaTrapezoidError z N +
        (logPhase z N + logPhase z ((N : ℝ) + 1)) / 2 -
          (logPhasePrimitive z ((N : ℝ) + 1) - logPhasePrimitive z N) := by
      simp only [gammaTrapezoidError, sum_range_succ, Nat.cast_add, Nat.cast_one]
      ring
    rw [he]
    push_cast
    constructor <;> linarith [ih.1, ih.2, hunit.1, hunit.2]

#print axioms gammaTrapezoidError_bound

end LiuWang.Proof.Campaign20260915.ZetaValidation
