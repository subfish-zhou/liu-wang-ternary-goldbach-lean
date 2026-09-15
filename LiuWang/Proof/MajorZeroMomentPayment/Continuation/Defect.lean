import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Uniform

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation

def endpointGap (N : ℕ) (beta : ℝ) : ℝ :=
  realEndpoint N beta - baseWeight N beta

def realDefect (N : ℕ) (beta eta : ℝ) : ℂ :=
  Jrho N beta eta - (baseWeight N beta : ℂ) * J N eta

theorem defect_weight_bounds {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (sourceWindowLower N) (N : ℝ)) :
    0 ≤ t^(beta - 1) - baseWeight N beta ∧
      t^(beta - 1) - baseWeight N beta ≤ endpointGap N beta := by
  have ha := window_lower_pos hN
  have hlo : baseWeight N beta ≤ t^(beta - 1) :=
    Real.rpow_le_rpow_of_nonpos (ha.trans_le ht.1) ht.2 (by linarith)
  have hhi : t^(beta - 1) ≤ realEndpoint N beta := by
    have he : sourceWindowLower N = 0.001 * (N : ℝ) := by unfold sourceWindowLower; ring
    exact Real.rpow_le_rpow_of_nonpos (he ▸ ha) (he ▸ ht.1) (by linarith)
  constructor
  · linarith
  · unfold endpointGap
    linarith

theorem endpointGap_nonneg {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1) :
    0 ≤ endpointGap N beta := by
  have h := defect_weight_bounds hN hb ⟨le_rfl, window_lower_le N⟩
  exact h.1.trans h.2

theorem realDefect_integral {N : ℕ} (hN : 0 < N) (beta eta : ℝ) :
    realDefect N beta eta =
      ∫ t in sourceWindowLower N..(N : ℝ),
        (t^(beta - 1) - baseWeight N beta : ℝ) • charReal (eta * t) := by
  have hj : IntervalIntegrable (fun t : ℝ => charReal (eta * t))
      volume (sourceWindowLower N) N :=
    (charReal_continuous.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [realDefect, Jrho, J, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (Jrho_intervalIntegrable hN beta eta) (hj.const_mul _)]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (window_lower_le N)] at ht
  dsimp only
  rw [real_cpow ((window_lower_pos hN).trans_le ht.1).le, Complex.real_smul]
  push_cast
  ring

theorem realDefect_mass {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1) (eta : ℝ) :
    ‖realDefect N beta eta‖ ≤ (N : ℝ) * endpointGap N beta := by
  rw [realDefect_integral hN]
  have hm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := sourceWindowLower N) (b := (N : ℝ)) (C := endpointGap N beta)
    (f := fun t => (t^(beta - 1) - baseWeight N beta : ℝ) • charReal (eta * t))
    (fun t ht => by
      rw [uIoc_of_le (window_lower_le N)] at ht
      have hw := defect_weight_bounds hN hb ⟨ht.1.le, ht.2⟩
      simpa only [norm_smul, Real.norm_eq_abs, charReal_norm, mul_one,
        abs_of_nonneg hw.1] using hw.2)
  rw [abs_of_nonneg (sub_nonneg.mpr (window_lower_le N))] at hm
  exact hm.trans (by nlinarith [endpointGap_nonneg hN hb, (window_lower_pos hN).le])

theorem realDefect_reciprocal {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    {eta : ℝ} (he : eta ≠ 0) :
    ‖realDefect N beta eta‖ ≤ endpointGap N beta / (Real.pi * |eta|) := by
  let a := sourceWindowLower N
  let c : ℂ := 2 * Real.pi * eta * Complex.I
  have ha : 0 < a := window_lower_pos hN
  have hab : a ≤ (N : ℝ) := window_lower_le N
  have hc : c ≠ 0 := by
    apply norm_ne_zero_iff.mp
    change ‖(2 * Real.pi * eta * Complex.I : ℂ)‖ ≠ 0
    rw [OscillatoryBounds.norm_frequency]
    positivity
  have hd : ∀ t ∈ Icc a (N : ℝ),
      HasDerivAt (fun x : ℝ => x^(beta - 1) - baseWeight N beta)
        ((beta - 1) * t^(beta - 1 - 1)) t := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (ha.trans_le ht.1).ne')).sub_const _
  have hg : ContinuousOn (fun t : ℝ => (beta - 1) * t^(beta - 1 - 1)) (Icc a N) :=
    continuousOn_const.mul (continuousOn_id.rpow_const
      (fun t ht => Or.inl (ha.trans_le ht.1).ne'))
  have hG : ∀ t ∈ Icc a (N : ℝ),
      HasDerivAt (fun x => charReal (eta * x) / c) (charReal (eta * t)) t := by
    intro t _
    simpa only [show (2 * Real.pi * eta * Complex.I : ℂ) = c from rfl,
      mul_div_cancel_right₀ _ hc] using
      (OscillatoryBounds.hasDerivAt_charReal_mul eta t).div_const c
  have hnorm (t : ℝ) : ‖charReal (eta * t) / c‖ ≤ 1 / (2 * Real.pi * |eta|) := by
    simp only [norm_div, charReal_norm, c, OscillatoryBounds.norm_frequency, le_refl]
  have h := OscillatoryBounds.norm_integral_weight_mul_le hab hd hg
    (fun t ht => (defect_weight_bounds hN hb ht).1)
    (fun t ht => mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (Real.rpow_nonneg (ha.trans_le ht.1).le _))
    hG (OscillatoryBounds.intervalIntegrable_charReal a N eta) (fun t _ => hnorm t)
  rw [realDefect_integral hN]
  have heq : a^(beta - 1) - baseWeight N beta = endpointGap N beta := by
    unfold a sourceWindowLower endpointGap realEndpoint
    congr 2
    ring
  rw [heq] at h
  simpa only [Complex.real_smul, show
    2 * endpointGap N beta * (1 / (2 * Real.pi * |eta|)) =
      endpointGap N beta / (Real.pi * |eta|) by ring] using h

end LiuWang.Proof.MajorZeroMomentPayment.Continuation
