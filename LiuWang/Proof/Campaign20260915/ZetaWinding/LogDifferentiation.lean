import LiuWang.Proof.Campaign20260915.ZetaWinding.LittlewoodPhase
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.DirichletZeroCount

theorem log_norm_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hn : f t ≠ 0) :
    HasDerivAt (fun u => Real.log ‖f u‖) (f' / f t).re t := by
  have hs : f t / f t ∈ slitPlane := by simp [hn, one_mem_slitPlane]
  have hd := (hf.div_const (f t)).clog_real hs
  have he : f' / f t / (f t / f t) = f' / f t := by simp [hn]
  rw [he] at hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have ha := hr.add_const (Real.log ‖f t‖)
  apply ha.congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.eventually_ne hn] with u hu
  dsimp
  rw [log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr hn)]
  ring

theorem zeta_log_norm_height_hasDerivAt {T x : ℝ} (hT : T ≠ 0)
    (hz : riemannZeta (horizontalAt T x) ≠ 0) :
    HasDerivAt (fun t => Real.log ‖riemannZeta (horizontalAt t x)‖)
      (-(logDeriv riemannZeta (horizontalAt T x)).im) T := by
  have hn : horizontalAt T x ≠ 1 := by
    intro he
    exact hT (by simpa [horizontalAt] using congrArg Complex.im he)
  have hd := (differentiableAt_riemannZeta hn).hasDerivAt.scomp T
    (((Complex.ofRealCLM.hasDerivAt (x := T)).mul_const I).const_add (x : ℂ))
  have h := log_norm_hasDerivAt hd hz
  convert! h using 1
  simp [horizontalAt, logDeriv_apply, smul_eq_mul, mul_div_assoc]

theorem log_zeta_hasDerivAt_right {s : ℂ} (hs : 2 ≤ s.re) :
    HasDerivAt (fun z => log (riemannZeta z)) (logDeriv riemannZeta s) s := by
  have hp : 0 < (riemannZeta s).re := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      Remainder.LFunction_re_pos (1 : LiuWang.Proof.Interfaces.Character 1) hs
  have hn : s ≠ 1 := by intro he; simp [he] at hs
  exact (differentiableAt_riemannZeta hn).hasDerivAt.clog
    (mem_slitPlane_iff.mpr (Or.inl hp))

theorem norm_logDeriv_zeta_decay {s : ℂ} (hs : 3 ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ 3 * 2 ^ (3 - s.re) := by
  have hr {z : ℂ} (hz : z ∈ Metric.closedBall s 1) : 2 ≤ z.re := by
    have hn : ‖z - s‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have he := neg_norm_le_re (z - s)
    simp only [sub_re] at he
    linarith
  have hd : DiffContOnCl ℂ (fun z => log (riemannZeta z)) (Metric.ball s 1) := by
    constructor
    · intro z hz
      exact (log_zeta_hasDerivAt_right (hr (Metric.ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt
    · rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
      exact fun z hz => (log_zeta_hasDerivAt_right (hr hz)).continuousAt.continuousWithinAt
  have hb (z : ℂ) (hz : z ∈ Metric.sphere s 1) :
      ‖log (riemannZeta z)‖ ≤ 3 * 2 ^ (3 - s.re) := by
    have hn : ‖z - s‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have he := neg_norm_le_re (z - s)
    simp only [sub_re] at he
    have hp : 2 - z.re ≤ 3 - s.re := by linarith
    exact (norm_log_zeta_decay (hr (Metric.sphere_subset_closedBall hz))).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp)
        (by norm_num))
  have h := norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1) hd hb
  simpa only [(log_zeta_hasDerivAt_right (by linarith : 2 ≤ s.re)).deriv, div_one] using h

theorem logDeriv_tail_integrable (T : ℝ) {a : ℝ} (ha : 3 ≤ a) :
    IntegrableOn (fun x => logDeriv riemannZeta (horizontalAt T x)) (Set.Ioi a) := by
  have he (x : ℝ) : (3 : ℝ) * 2 ^ (3 - x) = 2 * (3 * 2 ^ (2 - x)) := by
    rw [show (3 : ℝ) - x = 1 + (2 - x) by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  have hi : IntegrableOn (fun x : ℝ => (3 : ℝ) * 2 ^ (3 - x)) (Set.Ioi a) := by
    simp_rw [he]
    exact (log_tail_envelope_integrable a).const_mul 2
  have hc : ContinuousOn (fun x => logDeriv riemannZeta (horizontalAt T x)) (Set.Ioi a) := by
    intro x hx
    have hx' : a < x := hx
    have hs : 2 ≤ (horizontalAt T x).re := by simp [horizontalAt]; linarith
    have hn : horizontalAt T x ≠ 1 := by intro he; simp [he] at hs
    have hz := riemannZeta_ne_zero_of_one_le_re (by linarith : 1 ≤ (horizontalAt T x).re)
    have hzA := LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one hn
    exact ((hzA.deriv.continuousAt.div hzA.continuousAt hz).comp
      (f := horizontalAt T) (by unfold horizontalAt; fun_prop)).continuousWithinAt
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : a < x := hx
  simpa [horizontalAt] using
    norm_logDeriv_zeta_decay (s := horizontalAt T x) (by simp [horizontalAt]; linarith)

theorem log_zeta_horizontal_tendsto_zero (T : ℝ) :
    Tendsto (fun x => log (riemannZeta (horizontalAt T x))) atTop (𝓝 0) := by
  have he (x : ℝ) : (3 : ℝ) * 2 ^ (2 - x) = 12 * Real.exp (-(Real.log 2) * x) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_two,
      Real.rpow_def_of_pos (by norm_num), div_eq_mul_inv, ← Real.exp_neg]
    norm_num [neg_mul]
    ring
  have ht : Tendsto (fun x : ℝ => (3 : ℝ) * 2 ^ (2 - x)) atTop (𝓝 0) := by
    simp_rw [he]
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))))
    simpa using h.const_mul 12
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa [horizontalAt] using
    norm_log_zeta_decay (s := horizontalAt T x) (by simpa [horizontalAt] using hx)

theorem integral_logDeriv_right (T : ℝ) {a : ℝ} (ha : 3 ≤ a) :
    (∫ x in Set.Ioi a, logDeriv riemannZeta (horizontalAt T x)) =
      -log (riemannZeta (horizontalAt T a)) := by
  have hd (x : ℝ) (hx : x ∈ Set.Ici a) :
      HasDerivAt (fun u => log (riemannZeta (horizontalAt T u)))
        (logDeriv riemannZeta (horizontalAt T x)) x := by
    have hx' : a ≤ x := hx
    simpa [horizontalAt, Function.comp_def, smul_eq_mul] using
      (log_zeta_hasDerivAt_right (s := horizontalAt T x) (by simp [horizontalAt]; linarith)).scomp x
        ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((T : ℂ) * I))
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (logDeriv_tail_integrable T ha) (log_zeta_horizontal_tendsto_zero T)

#print axioms log_norm_hasDerivAt
#print axioms zeta_log_norm_height_hasDerivAt
#print axioms norm_logDeriv_zeta_decay
#print axioms integral_logDeriv_right

end LiuWang.Proof.Campaign20260915.ZetaWinding
