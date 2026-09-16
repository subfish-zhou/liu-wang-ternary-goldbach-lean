import LiuWang.Proof.Campaign20260915.RosserCount.BacklundPhaseLift

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.PrincipalPsi.Quantitative

theorem zeta_horizontal_regular_above_minus_two {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : -2 < x) : riemannZeta (horizontalAt T x) ≠ 0 := by
  intro hz
  have hs := zeta_zero_strip (by simpa [horizontalAt] using hx) hz
  exact hr _ hs.1 hs.2 (by simp [horizontalAt, abs_of_pos hT]) hz

private theorem horizontal_logDeriv_integrable_extended {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {a b : ℝ} (ha : -2 < a) (hb : -2 < b) :
    IntervalIntegrable (fun x => logDeriv riemannZeta (horizontalAt T x)) volume a b :=
  zeta_logDeriv_horizontal_integrable hT.ne' fun _x hx =>
    zeta_horizontal_regular_above_minus_two hT hr ((lt_min ha hb).trans_le hx.1)

theorem backlundLog_sub_critical {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : -2 < x) :
    backlundLog T x - backlundLog T (1 / 2) =
      HIntegral (logDeriv riemannZeta) (1 / 2) x T := by
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (horizontal_logDeriv_integrable_extended hT hr (by norm_num : (-2 : ℝ) < 1 / 2) hx)
    (horizontal_logDeriv_integrable_extended hT hr hx (by norm_num : (-2 : ℝ) < 2))
  change HIntegral (logDeriv riemannZeta) (1 / 2) x T +
    HIntegral (logDeriv riemannZeta) x 2 T =
      HIntegral (logDeriv riemannZeta) (1 / 2) 2 T at hi
  unfold backlundLog
  linear_combination -hi

def backlundArchSlope (T x : ℝ) : ℝ :=
  (1 / (horizontalAt T x - 1) +
    (1 / 2 : ℂ) * digamma (horizontalAt T x / 2 + 1)).im

theorem xi_horizontal_im_eq_zeta_arch {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : -2 < x) :
    (logDeriv riemannXi (horizontalAt T x)).im =
      (logDeriv riemannZeta (horizontalAt T x)).im + backlundArchSlope T x := by
  have hne : horizontalAt T x ≠ 1 := by
    intro he
    exact hT.ne' (by simpa [horizontalAt] using congrArg Complex.im he)
  have he := logDeriv_xi_eq_zeta (by simpa [horizontalAt] using hx) hne
    (zeta_horizontal_regular_above_minus_two hT hr hx)
  simpa only [backlundArchSlope, add_im, sub_im, div_ofNat_im, ofReal_im, zero_div,
    sub_zero, add_assoc] using congrArg Complex.im he

theorem backlund_logDeriv_reflection {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (-2 : ℝ) 3) :
    (logDeriv riemannZeta (horizontalAt T x)).im -
        (logDeriv riemannZeta (horizontalAt T (1 - x))).im =
      backlundArchSlope T (1 - x) - backlundArchSlope T x := by
  have hp : horizontalAt T (1 - x) = 1 - conj (horizontalAt T x) := by
    simp only [horizontalAt, map_add, map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  have he := congrArg Complex.im (Argument.xi_logDeriv_reflection (horizontalAt T x))
  rw [← hp, neg_im, conj_im, neg_neg] at he
  have hrx := xi_horizontal_im_eq_zeta_arch hT hr hx.1
  have hlx := xi_horizontal_im_eq_zeta_arch hT hr (by linarith [hx.2] : -2 < 1 - x)
  linarith only [he, hrx, hlx]

theorem backlundLog_reflection_defect {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4)) :
    ((backlundLog T (1 / 2 + δ)).im - (backlundLog T (1 / 2)).im) +
      ((backlundLog T (1 / 2 - δ)).im - (backlundLog T (1 / 2)).im) =
      ∫ u in (0 : ℝ)..δ,
        backlundArchSlope T (1 / 2 - u) - backlundArchSlope T (1 / 2 + u) := by
  let g : ℝ → ℂ := fun x => logDeriv riemannZeta (horizontalAt T x)
  have hu (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) δ) : 0 ≤ u ∧ u ≤ δ := by
    simpa only [Set.uIcc_of_le hδ.1, Set.mem_Icc] using hu
  have hiR : IntervalIntegrable (fun u => g (1 / 2 + u)) volume 0 δ := by
    apply ContinuousOn.intervalIntegrable
    intro u hum
    have hz := zeta_horizontal_regular_above_minus_two hT hr
      (by linarith [(hu u hum).1] : -2 < 1 / 2 + u)
    exact ((zeta_logDeriv_horizontal_continuousAt hT.ne' hz).comp
      (f := fun v : ℝ => 1 / 2 + v) (by fun_prop)).continuousWithinAt
  have hiL : IntervalIntegrable (fun u => g (1 / 2 - u)) volume 0 δ := by
    apply ContinuousOn.intervalIntegrable
    intro u hum
    have hz := zeta_horizontal_regular_above_minus_two hT hr
      (by linarith [(hu u hum).2, hδ.2] : -2 < 1 / 2 - u)
    exact ((zeta_logDeriv_horizontal_continuousAt hT.ne' hz).comp
      (f := fun v : ℝ => 1 / 2 - v) (by fun_prop)).continuousWithinAt
  have hR := intervalIntegral.integral_comp_add_left g (a := 0) (b := δ) (1 / 2 : ℝ)
  have hL := intervalIntegral.integral_comp_sub_left g (a := 0) (b := δ) (1 / 2 : ℝ)
  simp only [add_zero] at hR
  simp only [sub_zero] at hL
  rw [intervalIntegral.integral_symm (1 / 2 : ℝ) (1 / 2 - δ)] at hL
  have he :
      backlundLog T (1 / 2 + δ) - backlundLog T (1 / 2) +
        (backlundLog T (1 / 2 - δ) - backlundLog T (1 / 2)) =
      ∫ u in (0 : ℝ)..δ, g (1 / 2 + u) - g (1 / 2 - u) := by
    rw [backlundLog_sub_critical hT hr (by linarith [hδ.1] : -2 < 1 / 2 + δ),
      backlundLog_sub_critical hT hr (by linarith [hδ.2] : -2 < 1 / 2 - δ),
      intervalIntegral.integral_sub hiR hiL]
    change (∫ x in (1 / 2 : ℝ)..1 / 2 + δ, g x) +
      (∫ x in (1 / 2 : ℝ)..1 / 2 - δ, g x) =
        (∫ u in (0 : ℝ)..δ, g (1 / 2 + u)) -
          (∫ u in (0 : ℝ)..δ, g (1 / 2 - u))
    rw [hR, hL]
    ring
  have him := congrArg Complex.im he
  have hiIm :
      (∫ u in (0 : ℝ)..δ, g (1 / 2 + u) - g (1 / 2 - u)).im =
        ∫ u in (0 : ℝ)..δ, (g (1 / 2 + u) - g (1 / 2 - u)).im := by
    simpa only [Function.comp_def] using!
      (Complex.imCLM.intervalIntegral_comp_comm (hiR.sub hiL)).symm
  rw [hiIm] at him
  simp only [sub_im, add_im] at him
  refine him.trans ?_
  apply intervalIntegral.integral_congr
  intro u hum
  have hx : 1 / 2 + u ∈ Set.Ioo (-2 : ℝ) 3 := by
    constructor <;> linarith [(hu u hum).1, (hu u hum).2, hδ.2]
  have hp := backlund_logDeriv_reflection hT hr hx
  rw [show 1 - (1 / 2 + u) = 1 / 2 - u by ring] at hp
  exact hp

#print axioms zeta_horizontal_regular_above_minus_two
#print axioms backlundLog_sub_critical
#print axioms xi_horizontal_im_eq_zeta_arch
#print axioms backlund_logDeriv_reflection
#print axioms backlundLog_reflection_defect

end LiuWang.Proof.Campaign20260915.RosserCount
