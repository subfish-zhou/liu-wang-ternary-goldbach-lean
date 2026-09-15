import LiuWang.Proof.Campaign20260915.ZetaValidation.GammaTrapezoid

set_option autoImplicit false
noncomputable section

open Complex Filter Finset
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def gammaStirlingPhase (z : ℂ) : ℝ := ((z - 1 / 2) * log z - z).im

def gammaPhaseBoundary (z : ℂ) (N : ℕ) : ℝ :=
  z.im - ((z + N + 1 / 2) * log (1 + z / N)).im

theorem logGammaSeq_phase_identity {z : ℂ} (hz : 0 < z.re) {N : ℕ} (hN : 1 ≤ N) :
    (Complex.logGammaSeq z N).im =
      gammaStirlingPhase z + gammaPhaseBoundary z N - gammaTrapezoidError z N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNr.ne'
  have hplus : 1 + z / (N : ℂ) ≠ 0 := by
    apply ne_zero_of_re_pos
    rw [add_re, one_re, ← Complex.ofReal_natCast, Complex.div_ofReal_re]
    positivity
  have hmul : (N : ℂ) * (1 + z / N) = z + N := by field_simp; ring
  have hl : log (z + N) = (Real.log N : ℂ) + log (1 + z / N) := by
    rw [← hmul]
    simpa only [Complex.ofReal_natCast] using Complex.log_ofReal_mul hNr hplus
  simp [Complex.logGammaSeq, gammaStirlingPhase, gammaPhaseBoundary,
    gammaTrapezoidError, logPhase, logPhasePrimitive, mul_im, hl, log_im]
  ring

theorem gammaPhaseBoundary_tendsto_zero (z : ℂ) :
    Tendsto (gammaPhaseBoundary z) atTop (𝓝 0) := by
  have hmul : Tendsto (fun n : ℕ => (n : ℂ) * (z / n)) atTop (𝓝 z) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hmain := Complex.tendsto_nat_mul_log_one_add_of_tendsto hmul
  have hsmall : Tendsto (fun n : ℕ => z / (n : ℂ)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).ofReal.const_mul z
    simpa only [Function.comp_def, ofReal_inv, ofReal_natCast, ofReal_zero, mul_zero,
      div_eq_mul_inv] using h
  have hlog : Tendsto (fun n : ℕ => log (1 + z / (n : ℂ))) atTop (𝓝 0) := by
    have hc := hsmall.const_add 1
    simp only [add_zero] at hc
    simpa only [log_one, Function.comp_def] using!
      (Complex.differentiableAt_log (by simp : (1 : ℂ) ∈ slitPlane)).continuousAt.tendsto.comp
        hc
  have hp : Tendsto (fun n : ℕ => (z + n + 1 / 2) * log (1 + z / n)) atTop (𝓝 z) := by
    have h := (hlog.const_mul (z + 1 / 2)).add hmain
    simp only [mul_zero, zero_add] at h
    apply h.congr'
    exact Eventually.of_forall (fun n => by ring)
  have hpi := Complex.continuous_im.continuousAt.tendsto.comp hp
  simpa only [gammaPhaseBoundary, Function.comp_def, sub_self] using! hpi.const_sub z.im

theorem gammaStirlingPhase_error {z : ℂ} (hz : 0 < z.re) (ht : 0 ≤ z.im) :
    0 ≤ gammaStirlingPhase z - (gammaLogBranch z).im ∧
      gammaStirlingPhase z - (gammaLogBranch z).im ≤ z.im / (8 * normSq z) := by
  have hb : ∀ N : ℕ, gammaTrapezoidError z N ≤ z.im / (8 * normSq z) := by
    intro N
    have h := (gammaTrapezoidError_bound hz ht N).2
    have hg : logPhaseSlope z N ≤ 0 := by
      dsimp [logPhaseSlope]
      rw [inv_im]
      simp only [add_im, natCast_im, add_zero]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (normSq_nonneg _)
    have hzero : logPhaseSlope z 0 = -z.im / normSq z := by simp [logPhaseSlope, inv_im]
    rw [hzero] at h
    rw [neg_div] at h
    have he : z.im / (8 * normSq z) = (z.im / normSq z) / 8 := by ring
    rw [he]
    linarith
  have hg : Tendsto (fun N => (Complex.logGammaSeq z N).im) atTop (𝓝 (gammaLogBranch z).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp
      (Complex.cauchySeq_logGammaSeq hz).tendsto_limUnder
  have he : Tendsto (gammaTrapezoidError z) atTop
      (𝓝 (gammaStirlingPhase z - (gammaLogBranch z).im)) := by
    have h := ((gammaPhaseBoundary_tendsto_zero z).const_add (gammaStirlingPhase z)).sub hg
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hi := logGammaSeq_phase_identity hz hN
    linarith
  exact ⟨ge_of_tendsto he (Eventually.of_forall (fun N => (gammaTrapezoidError_bound hz ht N).1)),
    le_of_tendsto he (Eventually.of_forall hb)⟩

theorem gammaStirlingPhase_error_im {z : ℂ} (hz : 0 < z.re) (ht : 0 < z.im) :
    |(gammaLogBranch z).im - gammaStirlingPhase z| ≤ 1 / (8 * z.im) := by
  obtain ⟨hlo, hhi⟩ := gammaStirlingPhase_error hz ht.le
  rw [abs_of_nonpos (by linarith : (gammaLogBranch z).im - gammaStirlingPhase z ≤ 0)]
  have hn : 0 < normSq z := normSq_pos.mpr (ne_zero_of_re_pos hz)
  have hd : z.im / (8 * normSq z) ≤ 1 / (8 * z.im) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [normSq_apply]
    nlinarith [sq_nonneg z.re]
  linarith

def criticalGammaStirlingArgument (t : ℝ) : ℝ :=
  gammaStirlingPhase (criticalPoint t / 2) - t / 2 * Real.log Real.pi

theorem criticalGammaStirlingArgument_error {t : ℝ} (ht : 0 < t) :
    |criticalGammaArgument t - criticalGammaStirlingArgument t| ≤ 1 / (4 * t) := by
  have h := gammaStirlingPhase_error_im (z := criticalPoint t / 2)
    (by norm_num [criticalPoint, Complex.div_re, Complex.normSq_apply])
    (by simpa [criticalPoint, Complex.div_im, Complex.normSq_apply] using ht)
  have he : criticalGammaArgument t - criticalGammaStirlingArgument t =
      (gammaLogBranch (criticalPoint t / 2)).im - gammaStirlingPhase (criticalPoint t / 2) := by
    simp [criticalGammaArgument, criticalGammaStirlingArgument, criticalPoint, mul_im]
  rw [he]
  convert h using 1
  simp [criticalPoint]
  ring

theorem criticalGammaPhase_stirling_error {t : ℝ} (ht : 0 < t) :
    ‖criticalGammaPhase t -
      Complex.exp ((criticalGammaStirlingArgument t : ℂ) * I)‖ ≤ 1 / (4 * t) := by
  rw [criticalGammaPhase_eq_exp_argument]
  exact (unitPhase_distance_le _ _).trans (criticalGammaStirlingArgument_error ht)

#print axioms gammaStirlingPhase_error
#print axioms criticalGammaStirlingArgument_error
#print axioms criticalGammaPhase_stirling_error

end LiuWang.Proof.Campaign20260915.ZetaValidation
