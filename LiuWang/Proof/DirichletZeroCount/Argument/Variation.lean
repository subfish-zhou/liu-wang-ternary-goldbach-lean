import LiuWang.Proof.DirichletZeroCount.Argument.XiCount

/-! # The integrated logarithmic derivative is an actual continuous log lift -/

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate
open LiuWang.Proof.Interfaces (Character)
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Argument

theorem exp_integral_logarithmic_derivative {f f' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hfc : Continuous f')
    {a b : ℝ} (hn : ∀ x ∈ Set.uIcc a b, f x ≠ 0) :
    exp (∫ t in a..b, f' t / f t) * f a = f b := by
  let g : ℝ → ℂ := fun t => f' t / f t
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hgmeas : AEStronglyMeasurable g volume :=
    (hfc.measurable.div hcont.measurable).aestronglyMeasurable
  have hgc (x : ℝ) (hx : x ∈ Set.uIcc a b) : ContinuousAt g x :=
    hfc.continuousAt.div hcont.continuousAt (hn x hx)
  have hgi : IntervalIntegrable g volume a b :=
    (continuousOn_of_forall_continuousAt hgc).intervalIntegrable
  have hJ (x : ℝ) (hx : x ∈ Set.uIcc a b) :
      HasDerivAt (fun t : ℝ => ∫ v in a..t, g v) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hgi.mono (Set.uIcc_subset_uIcc Set.left_mem_uIcc hx) le_rfl)
      hgmeas.stronglyMeasurableAtFilter (hgc x hx)
  have hw (x : ℝ) (hx : x ∈ Set.uIcc a b) :
      HasDerivAt (fun t : ℝ => f t * exp (-(∫ v in a..t, g v))) 0 x := by
    convert! (hf x).mul (hJ x hx).neg.cexp using 1
    dsimp only [g]
    field_simp [hn x hx]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hw
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a b)
  have he : f b * exp (-(∫ t in a..b, g t)) = f a := by
    have hh : (0 : ℂ) = f b * exp (-(∫ t in a..b, g t)) - f a := by
      simpa only [intervalIntegral.integral_zero, intervalIntegral.integral_same, neg_zero,
        exp_zero, mul_one] using hint
    exact sub_eq_zero.mp hh.symm
  calc
    exp (∫ t in a..b, f' t / f t) * f a =
        exp (∫ t in a..b, g t) * (f b * exp (-(∫ t in a..b, g t))) := by rw [he]
    _ = f b := by rw [mul_left_comm, ← exp_add]; simp

def linePoint (z v : ℂ) (t : ℝ) : ℂ := z + (t : ℂ) * v
def lineLogIntegral (F : ℂ → ℂ) (z v : ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, v * logDeriv F (linePoint z v t)

theorem line_hasDerivAt (z v : ℂ) (t : ℝ) :
    HasDerivAt (linePoint z v) v t := by
  convert! (hasDerivAt_const t z).add ((Complex.ofRealCLM.hasDerivAt).mul_const v) using 1
  simp

theorem line_exp_integral {F : ℂ → ℂ} (hF : Differentiable ℂ F) (z v : ℂ)
    {a b : ℝ} (hn : ∀ t ∈ Set.uIcc a b, F (linePoint z v t) ≠ 0) :
    exp (lineLogIntegral F z v a b) * F (linePoint z v a) = F (linePoint z v b) := by
  have hd (t : ℝ) : HasDerivAt (fun x => F (linePoint z v x))
      (deriv F (linePoint z v t) * v) t := by
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using
      (hF.differentiableAt.hasDerivAt).scomp t (line_hasDerivAt z v t)
  have hc : Continuous (fun t => deriv F (linePoint z v t) * v) := by
    have hcd : Continuous (deriv F) :=
      continuous_iff_continuousAt.mpr (fun s => (hF.analyticAt s).deriv.continuousAt)
    exact (hcd.comp (by unfold linePoint; fun_prop)).mul_const v
  have h := exp_integral_logarithmic_derivative hd hc hn
  simpa only [lineLogIntegral, logDeriv_apply, mul_div_assoc, div_mul_eq_mul_div, mul_comm,
    mul_left_comm, mul_assoc] using h

theorem line_continuous_log_lift {F : ℂ → ℂ} (hF : Differentiable ℂ F) (z v : ℂ)
    {a b : ℝ} (hn : ∀ t ∈ Set.uIcc a b, F (linePoint z v t) ≠ 0)
    (w : ℂ) (hw : exp w = F (linePoint z v a)) :
    ContinuousOn (fun t => w + lineLogIntegral F z v a t)
      (Set.uIcc a b) ∧
    (∀ t ∈ Set.uIcc a b,
      exp (w + lineLogIntegral F z v a t) = F (linePoint z v t)) ∧
    (w + lineLogIntegral F z v a b).im -
      (w + lineLogIntegral F z v a a).im =
        (lineLogIntegral F z v a b).im := by
  have hc : ContinuousOn (fun t => v * logDeriv F (linePoint z v t)) (Set.uIcc a b) := by
    intro t ht
    exact (continuousAt_const.mul (((hF.analyticAt _).deriv.div (hF.analyticAt _) (hn t ht)).continuousAt.comp
      (line_hasDerivAt z v t).continuousAt)).continuousWithinAt
  refine ⟨continuousOn_const.add
    (intervalIntegral.continuousOn_primitive_interval' hc.intervalIntegrable Set.left_mem_uIcc), ?_, ?_⟩
  · intro t ht
    rw [exp_add, hw, mul_comm]
    exact line_exp_integral hF z v (fun x hx => hn x (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht hx))
  · simp [lineLogIntegral]

theorem horizontal_exp_integral {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b t : ℝ} (hn : ∀ x ∈ Set.uIcc a b, F ((x : ℂ) + (t : ℂ) * I) ≠ 0) :
    exp (HIntegral (logDeriv F) a b t) * F ((a : ℂ) + (t : ℂ) * I) =
      F ((b : ℂ) + (t : ℂ) * I) := by
  simpa [lineLogIntegral, linePoint, HIntegral, add_comm] using
    line_exp_integral hF ((t : ℂ) * I) 1 (by simpa [linePoint, add_comm] using hn)

theorem vertical_exp_integral {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {b a c : ℝ} (hn : ∀ t ∈ Set.uIcc a c, F ((b : ℂ) + (t : ℂ) * I) ≠ 0) :
    exp (VIntegral (logDeriv F) b a c) * F ((b : ℂ) + (a : ℂ) * I) =
      F ((b : ℂ) + (c : ℂ) * I) := by
  simpa only [lineLogIntegral, linePoint, intervalIntegral.integral_const_mul,
    VIntegral, smul_eq_mul] using line_exp_integral hF (b : ℂ) I hn

end LiuWang.Proof.DirichletZeroCount.Argument
