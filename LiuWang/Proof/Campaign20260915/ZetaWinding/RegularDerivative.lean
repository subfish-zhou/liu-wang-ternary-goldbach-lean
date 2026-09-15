import LiuWang.Proof.Campaign20260915.ZetaWinding.LogDifferentiation

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem regular_height_neighborhood {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    ∃ e : ℝ, 0 < e ∧ ∀ t ∈ Metric.closedBall T e,
      0 < t ∧ ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = t → riemannZeta s ≠ 0 := by
  classical
  let F := (zetaClosedValues (T + 1)).image (fun z => |z.im|)
  have hn : T ∉ (F : Set ℝ) := by
    intro hm
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hm
    obtain ⟨hz, h0, h1, _⟩ := mem_zetaClosedValues.mp hz
    exact hr z h0 h1 he hz
  have hu : Set.Ioo 0 (T + 1) ∩ (F : Set ℝ)ᶜ ∈ 𝓝 T :=
    inter_mem (Ioo_mem_nhds hT (by linarith)) (F.finite_toSet.isClosed.isOpen_compl.mem_nhds hn)
  obtain ⟨r, hr0, hsub⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨r / 2, by positivity, ?_⟩
  intro t ht
  have ht' := hsub (lt_of_le_of_lt ht (by linarith : r / 2 < r))
  refine ⟨ht'.1.1, ?_⟩
  intro z h0 h1 he hz
  apply ht'.2
  exact Finset.mem_image.mpr ⟨z,
    mem_zetaClosedValues.mpr ⟨hz, h0, h1, by rw [he]; exact ht'.1.2.le⟩, he⟩

theorem regular_logDeriv_uniform_bound {T e : ℝ}
    (hr : ∀ t ∈ Metric.closedBall T e,
      0 < t ∧ ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = t → riemannZeta s ≠ 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ Metric.closedBall T e, ∀ x : ℝ, 1 / 2 ≤ x →
      ‖logDeriv riemannZeta (horizontalAt t x)‖ ≤ C * (2 * (3 * 2 ^ (2 - x))) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => logDeriv riemannZeta (horizontalAt p.1 p.2))
      (Metric.closedBall T e ×ˢ Set.Icc (1 / 2 : ℝ) 3) := by
    intro p hp
    have ht := hr p.1 hp.1
    have hz := zeta_horizontal_regular ht.1 ht.2 hp.2.1
    have hn : horizontalAt p.1 p.2 ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp [horizontalAt] at hi
      linarith [ht.1]
    have ha := LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one hn
    exact ((ha.deriv.continuousAt.div ha.continuousAt hz).comp
      (f := fun p : ℝ × ℝ => horizontalAt p.1 p.2)
      (by unfold horizontalAt; fun_prop)).continuousWithinAt
  obtain ⟨M, hM⟩ := ((isCompact_closedBall T e).prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max M 1, le_max_right _ _, ?_⟩
  intro t ht x hx
  have he : 2 * (3 * (2 : ℝ) ^ (2 - x)) = 3 * 2 ^ (3 - x) := by
    rw [show (3 : ℝ) - x = 1 + (2 - x) by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  rw [he]
  by_cases hx3 : x ≤ 3
  · have hb := hM (t, x) ⟨ht, hx, hx3⟩
    have hpow : 1 ≤ (2 : ℝ) ^ (3 - x) := Real.one_le_rpow (by norm_num) (by linarith)
    have hC : 0 ≤ max M 1 := le_trans (by norm_num) (le_max_right _ _)
    nlinarith [le_max_left M 1]
  · have hb := norm_logDeriv_zeta_decay (s := horizontalAt t x)
      (by simpa [horizontalAt] using (not_le.mp hx3).le)
    have hC : 1 ≤ max M 1 := le_max_right _ _
    have hp : 0 ≤ 3 * (2 : ℝ) ^ (3 - x) := by positivity
    simp only [horizontalAt, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at hb
    exact hb.trans (le_mul_of_one_le_left hp hC)

theorem horizontalLogMass_hasDerivAt_integral {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    IntegrableOn (fun x => -(logDeriv riemannZeta (horizontalAt T x)).im)
      (Set.Ioi (1 / 2 : ℝ)) ∧
    HasDerivAt horizontalLogMass
      (∫ x in Set.Ioi (1 / 2 : ℝ), -(logDeriv riemannZeta (horizontalAt T x)).im) T := by
  obtain ⟨e, he, hreg⟩ := regular_height_neighborhood hT hr
  obtain ⟨C, _, hC⟩ := regular_logDeriv_uniform_bound hreg
  have hs := Metric.closedBall_mem_nhds T he
  have hmeas : ∀ᶠ t in 𝓝 T, AEStronglyMeasurable
      (fun x => Real.log ‖riemannZeta (horizontalAt t x)‖)
      (volume.restrict (Set.Ioi (1 / 2 : ℝ))) := by
    filter_upwards [hs] with t ht
    exact (zeta_horizontal_log_integrable_Ioi (hreg t ht).1.ne' (1 / 2)).aestronglyMeasurable
  have hdermeas : AEStronglyMeasurable
      (fun x => -(logDeriv riemannZeta (horizontalAt T x)).im)
      (volume.restrict (Set.Ioi (1 / 2 : ℝ))) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hc := zeta_logDeriv_horizontal_continuousAt hT.ne'
      (zeta_horizontal_regular hT hr (show 1 / 2 ≤ x from hx.le))
    exact (Complex.continuous_im.continuousAt.comp hc).neg.continuousWithinAt
  have hi : IntegrableOn (fun x : ℝ => C * (2 * (3 * 2 ^ (2 - x))))
      (Set.Ioi (1 / 2 : ℝ)) :=
    ((log_tail_envelope_integrable (1 / 2)).const_mul 2).const_mul C
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas
    (F' := fun t x => -(logDeriv riemannZeta (horizontalAt t x)).im)
    (zeta_horizontal_log_integrable_Ioi hT.ne' (1 / 2)) hdermeas ?_ hi ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro t ht
    simpa only [Real.norm_eq_abs, abs_neg] using
      (abs_im_le_norm _).trans (hC t ht x (show 1 / 2 ≤ x from hx.le))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro t ht
    have hr' := hreg t ht
    exact zeta_log_norm_height_hasDerivAt hr'.1.ne'
      (zeta_horizontal_regular hr'.1 hr'.2 (show 1 / 2 ≤ x from hx.le))

#print axioms regular_height_neighborhood
#print axioms regular_logDeriv_uniform_bound
#print axioms horizontalLogMass_hasDerivAt_integral

end LiuWang.Proof.Campaign20260915.ZetaWinding
