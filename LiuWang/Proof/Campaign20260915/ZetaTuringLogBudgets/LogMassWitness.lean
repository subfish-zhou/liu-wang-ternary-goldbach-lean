import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.CriticalStripWitness

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

def sourceHorizontalLogBudget (T : ℝ) : ℝ :=
  (∫ x in (1 / 2 : ℝ)..(5 / 4), Real.log (sourceStripNormEnvelope (horizontalAt T x))) +
    154345861 / 120000000

theorem sourceStripNormEnvelope_pos {s : ℂ} (hs : s ≠ 1) :
    0 < sourceStripNormEnvelope s := by
  have hD := norm_pos_iff.mpr (sourceStripNormalizer_ne_zero s)
  have hE := norm_pos_iff.mpr (sourceBottomBarrier_ne_zero s)
  have hS : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs)
  unfold sourceStripNormEnvelope
  positivity

theorem sourceStripNormEnvelope_ge_one {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 1 ≤ s.im) :
    1 ≤ sourceStripNormEnvelope s := by
  have hs0 : 0 < s.re := by linarith [hs.1]
  have ht0 : 0 < s.im := by linarith
  have hs1 : s ≠ 1 := by intro h; simp [h] at ht0
  have hn1 : 1 ≤ ‖s‖ := ht.trans ((le_abs_self _).trans (Complex.abs_im_le_norm s))
  have hD : ‖s‖ ≤ ‖sourceStripNormalizer s‖ := by
    calc
      ‖s‖ = ‖s‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ‖s‖ ^ (17 / 12 - s.re / 3) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hs.2])
      _ ≤ _ := sourceStripNormalizer_norm_lower hs0 ht0
  have hB : 0 ≤ (sourceStripBoundaryExponent s).re := by
    rw [sourceStripBoundaryExponent_re]
    have h0 : 0 ≤ (5 / 4 : ℝ) - s.re := by linarith [hs.2]
    have h1 : 0 ≤ s.re - (1 / 2 : ℝ) := by linarith [hs.1]
    have hK : 0 ≤ Real.log (253 / 100 : ℝ) := Real.log_nonneg (by norm_num)
    have hL := realLogZeta_nonneg (by norm_num : (1 : ℝ) < 5 / 4)
    positivity
  have hnorm : ‖s - 1‖ ≤ ‖s‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, one_re, one_im, sub_zero]
    nlinarith [hs.1]
  unfold sourceStripNormEnvelope
  rw [one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))]
  exact (hnorm.trans hD).trans ((le_mul_of_one_le_right (norm_nonneg _)
    (Real.one_le_exp hB)).trans (le_mul_of_one_le_right (by positivity)
      (sourceBottomBarrier_norm_ge_one hs)))

theorem sourceStripNormEnvelope_horizontal_continuous {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun x => sourceStripNormEnvelope (horizontalAt T x)) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hs : 0 < (horizontalAt T x).re := by simpa [horizontalAt] using hx
  have hp : ContinuousAt (horizontalAt T) x := by unfold horizontalAt; fun_prop
  have hD := (sourceStripNormalizer_differentiableAt hs).continuousAt.comp hp
  have hB : Continuous sourceStripBoundaryExponent := by
    unfold sourceStripBoundaryExponent
    fun_prop
  have hE := sourceBottomBarrier_differentiable.continuous.continuousAt.comp hp
  have hs1 : horizontalAt T x ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp [horizontalAt] at hi
    linarith
  exact (((hD.norm.mul ((Complex.continuous_re.continuousAt.comp
    (hB.continuousAt.comp hp)).rexp)).mul hE.norm).div
      (hp.sub continuousAt_const).norm
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1))).continuousWithinAt

theorem sourceStripLogEnvelope_intervalIntegrable {T : ℝ} (hT : 0 < T) :
    IntervalIntegrable (fun x => Real.log (sourceStripNormEnvelope (horizontalAt T x)))
      volume (1 / 2) (5 / 4) := by
  have hlog : ContinuousOn (fun x => Real.log (sourceStripNormEnvelope (horizontalAt T x)))
      (Set.Ioi (0 : ℝ)) := by
    apply (sourceStripNormEnvelope_horizontal_continuous hT).log
    intro x _
    apply (sourceStripNormEnvelope_pos (s := horizontalAt T x) _).ne'
    intro h
    have hi := congrArg Complex.im h
    simp [horizontalAt] at hi
    linarith
  apply ContinuousOn.intervalIntegrable
  apply hlog.mono
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hx
  change 0 < x
  linarith [hx.1]

theorem sourceStrip_log_violation_critical_witness {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 128 * Real.pi ≤ s.im)
    (hbad : Real.log (sourceStripNormEnvelope s) < Real.log ‖riemannZeta s‖) :
    ∃ t : ℝ, 128 * Real.pi ≤ t ∧
      (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖ := by
  have ht1 : 1 ≤ s.im := by linarith [Real.pi_gt_three]
  have hM := sourceStripNormEnvelope_ge_one hs ht1
  have hn : 0 < ‖riemannZeta s‖ := by
    by_contra h
    have hz : ‖riemannZeta s‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [hz, Real.log_zero] at hbad
    linarith [Real.log_nonneg hM]
  have hnorm : sourceStripNormEnvelope s < ‖riemannZeta s‖ := by
    by_contra h
    exact (not_le_of_gt hbad) (Real.log_le_log hn (not_lt.mp h))
  exact sourceStrip_norm_violation_critical_witness hs ht hnorm

theorem sourceStrip_integral_violation_critical_witness {T : ℝ} (hT : 128 * Real.pi ≤ T)
    (hbad : (∫ x in (1 / 2 : ℝ)..(5 / 4),
      Real.log (sourceStripNormEnvelope (horizontalAt T x))) <
      ∫ x in (1 / 2 : ℝ)..(5 / 4), Real.log ‖riemannZeta (horizontalAt T x)‖) :
    ∃ t : ℝ, 128 * Real.pi ≤ t ∧
      (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖ := by
  have ht : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hex : ∃ x : ℝ, x ∈ Set.Icc (1 / 2 : ℝ) (5 / 4) ∧
      Real.log (sourceStripNormEnvelope (horizontalAt T x)) <
        Real.log ‖riemannZeta (horizontalAt T x)‖ := by
    by_contra h
    push Not at h
    have hle := intervalIntegral.integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)
      (zeta_horizontal_log_integrable ht.ne' (1 / 2) (5 / 4))
      (sourceStripLogEnvelope_intervalIntegrable ht) h
    exact (not_le_of_gt hbad) hle
  obtain ⟨x, hx, hlog⟩ := hex
  exact sourceStrip_log_violation_critical_witness
    (by simpa [horizontalAt] using hx) (by simpa [horizontalAt] using hT) hlog

theorem horizontalLogMass_violation_critical_witness {T : ℝ} (hT : 128 * Real.pi ≤ T)
    (hbad : sourceHorizontalLogBudget T < horizontalLogMass T) :
    ∃ t : ℝ, 128 * Real.pi ≤ t ∧
      (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) < ‖riemannZeta (criticalPoint t)‖ := by
  have ht : 0 < T := lt_of_lt_of_le (by positivity) hT
  have h := horizontalLogMass_numeric_upper ht.ne'
  apply sourceStrip_integral_violation_critical_witness hT
  unfold sourceHorizontalLogBudget at hbad
  linarith

#print axioms sourceStripNormEnvelope_ge_one
#print axioms sourceStripLogEnvelope_intervalIntegrable
#print axioms sourceStrip_integral_violation_critical_witness
#print axioms horizontalLogMass_violation_critical_witness

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
