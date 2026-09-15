import LiuWang.Proof.DirichletZeroCount.Remainder.RightHalfPlane

/-! # Actual continuous logarithms pay the ordinary L right vertical edge -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem LFunction_analyticAt_of_re_two {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : 2 ≤ s.re) : AnalyticAt ℂ chi.LFunction s := by
  have hn : s ≠ 1 := by intro h; simp [h] at hs
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [isOpen_compl_singleton.mem_nhds hn] with z hz
  exact chi.differentiableAt_LFunction z (Or.inl hz)

theorem vertical_L_log_hasDerivAt {q : ℕ} [NeZero q] (chi : Character q)
    {b : ℝ} (hb : 2 ≤ b) (t : ℝ) :
    HasDerivAt (fun x : ℝ => log (chi.LFunction ((b : ℂ) + (x : ℂ) * I)))
      (I * logDeriv chi.LFunction ((b : ℂ) + (t : ℂ) * I)) t := by
  have hs : 2 ≤ ((b : ℂ) + (t : ℂ) * I).re := by simpa using hb
  have hd := ((LFunction_analyticAt_of_re_two chi hs).differentiableAt.hasDerivAt).scomp t
    (Argument.line_hasDerivAt (b : ℂ) I t)
  have hn : chi.LFunction ((b : ℂ) + (t : ℂ) * I) ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (LFunction_re_pos chi hs))
  simpa only [Argument.linePoint, Function.comp_def, smul_eq_mul, logDeriv_apply,
    mul_comm, mul_div_assoc] using! hd.clog_real hn

theorem vertical_L_logDeriv_continuous {q : ℕ} [NeZero q] (chi : Character q)
    {b : ℝ} (hb : 2 ≤ b) :
    Continuous (fun t : ℝ => I * logDeriv chi.LFunction ((b : ℂ) + (t : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : 2 ≤ ((b : ℂ) + (t : ℂ) * I).re := by simpa using hb
  have ha := LFunction_analyticAt_of_re_two chi hs
  have hn : chi.LFunction ((b : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hp := LFunction_re_pos chi hs
    simp [h] at hp
  have hc := (ha.deriv.div ha hn).continuousAt.comp (f := fun x : ℝ => (b : ℂ) + (x : ℂ) * I)
    (show ContinuousAt (fun x : ℝ => (b : ℂ) + (x : ℂ) * I) t by fun_prop)
  simpa only [logDeriv_apply, Function.comp_def, Pi.mul_apply, Pi.div_apply] using!
    (continuousAt_const (y := I)).mul hc

theorem vertical_L_eq_log_sub {q : ℕ} [NeZero q] (chi : Character q)
    {b : ℝ} (hb : 2 ≤ b) (a c : ℝ) :
    VIntegral (logDeriv chi.LFunction) b a c =
      log (chi.LFunction ((b : ℂ) + (c : ℂ) * I)) -
        log (chi.LFunction ((b : ℂ) + (a : ℂ) * I)) := by
  rw [VIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => vertical_L_log_hasDerivAt chi hb t)
    ((vertical_L_logDeriv_continuous chi hb).intervalIntegrable a c)

theorem vertical_L_continuous_log {q : ℕ} [NeZero q] (chi : Character q)
    {b : ℝ} (hb : 2 ≤ b) :
    Continuous (fun t : ℝ => log (chi.LFunction ((b : ℂ) + (t : ℂ) * I))) ∧
      ∀ t : ℝ, exp (log (chi.LFunction ((b : ℂ) + (t : ℂ) * I))) =
        chi.LFunction ((b : ℂ) + (t : ℂ) * I) := by
  refine ⟨continuous_iff_continuousAt.mpr (fun t => (vertical_L_log_hasDerivAt chi hb t).continuousAt), ?_⟩
  intro t
  apply exp_log
  intro he
  have hp := LFunction_re_pos chi (show 2 ≤ ((b : ℂ) + (t : ℂ) * I).re by simpa using hb)
  simp [he] at hp

theorem vertical_L_im_abs_lt_pi {q : ℕ} [NeZero q] (chi : Character q)
    {b : ℝ} (hb : 2 ≤ b) (a c : ℝ) :
    |(VIntegral (logDeriv chi.LFunction) b a c).im| < Real.pi := by
  rw [vertical_L_eq_log_sub chi hb, sub_im, log_im, log_im]
  have hp (t : ℝ) : |(chi.LFunction ((b : ℂ) + (t : ℂ) * I)).arg| < Real.pi / 2 :=
    abs_arg_lt_pi_div_two_iff.mpr (Or.inl
      (LFunction_re_pos chi (by simpa using hb)))
  exact (abs_sub _ _).trans_lt (by linarith [hp a, hp c])

theorem completed_count_le_horizontal {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 2 ≤ b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    (count chi 0 H : ℝ) ≤
      (H * Real.log ((q : ℝ) / Real.pi) +
        (HIntegral (logDeriv chi.LFunction) (1 / 2) b (-H)).im -
        (HIntegral (logDeriv chi.LFunction) (1 / 2) b H).im + Real.pi +
        (if chi.Even then sourceGammaMain (1 / 2) H else sourceGammaMain (3 / 2) H)) / Real.pi := by
  apply (completed_count_le_sourceGamma (b := b) hchi hprim (by linarith) hH hreg).trans
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have hv := (le_abs_self _).trans (vertical_L_im_abs_lt_pi chi hb (-H) H).le
  simp only [Argument.rightThreeIntegral, sub_im, add_im]
  linarith

end LiuWang.Proof.DirichletZeroCount.Remainder
