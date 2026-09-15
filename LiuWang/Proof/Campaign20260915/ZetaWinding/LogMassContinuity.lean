import LiuWang.Proof.Campaign20260915.ZetaWinding.RegularLittlewood

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

theorem horizontal_zero_log_integral_continuous (rho : ℂ) (a b : ℝ) :
    Continuous (fun t => ∫ x in a..b, Real.log ‖horizontalAt t x - rho‖) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  have hc : Continuous (fun p : ℝ × ℝ => horizontalAt p.1 p.2 - rho) := by
    unfold horizontalAt
    fun_prop
  obtain ⟨M, hM⟩ := ((isCompact_closedBall T 1).prod
    (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hc.continuousOn
  let B : ℝ → ℝ := fun x => |Real.log (|x - rho.re|)| + |Real.log (max M 1)|
  have hi : IntervalIntegrable B volume a b := by
    have hk := log_norm_zero_factor_integrable rho rho.im a b
    have he (x : ℝ) : horizontalAt rho.im x - rho = ((x - rho.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [horizontalAt]
    have hk' : IntervalIntegrable (fun x => Real.log (|x - rho.re|)) volume a b := by
      convert! hk using 1
      funext x
      rw [he, norm_real, Real.norm_eq_abs]
    exact hk'.abs.add (intervalIntegrable_const (c := |Real.log (max M 1)|))
  refine intervalIntegral.continuousAt_of_dominated_interval
    (Eventually.of_forall (fun t =>
      (log_norm_zero_factor_integrable rho t a b).aestronglyMeasurable_restrict_uIoc))
    ?_ hi ?_
  · filter_upwards [Metric.closedBall_mem_nhds T (by norm_num : (0 : ℝ) < 1)] with t ht
    filter_upwards [volume.ae_ne rho.re] with x hx hxI
    have hlo : 0 < |x - rho.re| := abs_pos.mpr (sub_ne_zero.mpr hx)
    have hl : |x - rho.re| ≤ ‖horizontalAt t x - rho‖ := by
      simpa [horizontalAt] using abs_re_le_norm (horizontalAt t x - rho)
    have hu : ‖horizontalAt t x - rho‖ ≤ max M 1 :=
      (hM (t, x) ⟨ht, Set.uIoc_subset_uIcc hxI⟩).trans (le_max_left _ _)
    have hll := Real.log_le_log hlo hl
    have hlu := Real.log_le_log (hlo.trans_le hl) hu
    rw [Real.norm_eq_abs, abs_le]
    dsimp [B]
    constructor
    · linarith [neg_abs_le (Real.log (|x - rho.re|)), abs_nonneg (Real.log (max M 1))]
    · linarith [le_abs_self (Real.log (max M 1)), abs_nonneg (Real.log (|x - rho.re|))]
  · filter_upwards [volume.ae_ne rho.re] with x hx _
    have hn : horizontalAt T x - rho ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp [horizontalAt] at hr
      exact hx (by linarith)
    exact (hc.comp (by fun_prop : Continuous (fun t : ℝ => (t, x)))).continuousAt.norm.log
      (norm_ne_zero_iff.mpr hn)

theorem zeta_finite_horizontal_log_continuousAt (T a b : ℝ) :
    ContinuousAt (fun t => ∫ x in a..b, Real.log ‖riemannZeta (horizontalAt t x)‖) T := by
  classical
  let K := (fun p : ℝ × ℝ => horizontalAt p.1 p.2) ''
    (Metric.closedBall T 1 ×ˢ Set.uIcc a b)
  have hK : IsCompact K :=
    ((isCompact_closedBall T 1).prod isCompact_uIcc).image
      (by unfold horizontalAt; fun_prop)
  have hpoint {t x : ℝ} (ht : t ∈ Metric.closedBall T 1) (hx : x ∈ Set.uIcc a b) :
      horizontalAt t x ∈ K := ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  have hf : MeromorphicOn riemannZeta K := by
    intro s _
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      LiuWang.Proof.PrincipalPsi.meromorphic_principal 1 s
  have ho : ∀ s : K, meromorphicOrderAt riemannZeta s ≠ ⊤ := by
    intro s
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      LiuWang.Proof.PrincipalPsi.meromorphicOrderAt_principal_ne_top 1 s
  let D := MeromorphicOn.divisor riemannZeta K
  have hD : D.support.Finite := D.finiteSupport hK
  obtain ⟨g, hg, hgn, he⟩ := hf.extract_zeros_poles ho hD
  have hlog := MeromorphicOn.extract_zeros_poles_log hgn he
  let F := hD.toFinset
  have hsum : (∑ᶠ rho : ℂ, fun s : ℂ => (D rho : ℝ) * Real.log ‖s - rho‖) =
      ∑ rho ∈ F, fun s : ℂ => (D rho : ℝ) * Real.log ‖s - rho‖ := by
    apply finsum_eq_sum_of_support_subset
    intro rho hr
    by_contra hn
    have hzero : D rho = 0 := by
      simpa [F, Function.mem_support] using hn
    apply hr
    funext s
    simp [hzero]
  rw [hsum] at hlog
  let E := {s : ℂ | Real.log ‖riemannZeta s‖ =
    (∑ rho ∈ F, (D rho : ℝ) * Real.log ‖s - rho‖) + Real.log ‖g s‖}
  have hE : E ∈ codiscreteWithin K := by
    filter_upwards [hlog] with s hs
    simpa only [E, Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_apply] using hs
  have hbad := hK.finite_sdiff_of_mem_codiscreteWithin hE
  have hgC : ContinuousOn (fun p : ℝ × ℝ => Real.log ‖g (horizontalAt p.1 p.2)‖)
      (Metric.closedBall T 1 ×ˢ Set.uIcc a b) := by
    intro p hp
    have hs := hpoint hp.1 hp.2
    exact (((hg _ hs).continuousAt.comp
      (f := fun p : ℝ × ℝ => horizontalAt p.1 p.2) (by unfold horizontalAt; fun_prop)).norm.log
        (norm_ne_zero_iff.mpr (hgn ⟨_, hs⟩))).continuousWithinAt
  have hgI (t : ℝ) (ht : t ∈ Metric.closedBall T 1) :
      IntervalIntegrable (fun x => Real.log ‖g (horizontalAt t x)‖) volume a b :=
    (hgC.comp (by fun_prop : ContinuousOn (fun x : ℝ => (t, x)) (Set.uIcc a b))
      (fun _ hx => ⟨ht, hx⟩)).intervalIntegrable
  obtain ⟨C, hC⟩ := ((isCompact_closedBall T 1).prod isCompact_uIcc).exists_bound_of_continuousOn hgC
  have hgInt : ContinuousAt (fun t => ∫ x in a..b, Real.log ‖g (horizontalAt t x)‖) T := by
    refine intervalIntegral.continuousAt_of_dominated_interval
      (Eventually.mono (Metric.closedBall_mem_nhds T (by norm_num : (0 : ℝ) < 1))
        (fun t ht => (hgI t ht).aestronglyMeasurable_restrict_uIoc)) ?_
      (intervalIntegrable_const (c := C)) ?_
    · filter_upwards [Metric.closedBall_mem_nhds T (by norm_num : (0 : ℝ) < 1)] with t ht
      exact Eventually.of_forall (fun x hx => hC (t, x) ⟨ht, Set.uIoc_subset_uIcc hx⟩)
    · exact Eventually.of_forall (fun x hx => by
        have hs := hpoint (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))
          (Set.uIoc_subset_uIcc hx)
        exact (((hg _ hs).continuousAt.comp
          (f := fun t => horizontalAt t x) (by unfold horizontalAt; fun_prop)).norm.log
          (norm_ne_zero_iff.mpr (hgn ⟨_, hs⟩))))
  have hmodel : ContinuousAt (fun t =>
      (∑ rho ∈ F, (D rho : ℝ) * ∫ x in a..b, Real.log ‖horizontalAt t x - rho‖) +
        ∫ x in a..b, Real.log ‖g (horizontalAt t x)‖) T :=
    (continuous_finsetSum F (fun rho _ =>
      (horizontal_zero_log_integral_continuous rho a b).const_mul _)).continuousAt.add hgInt
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Metric.closedBall_mem_nhds T (by norm_num : (0 : ℝ) < 1)] with t ht
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc a b →
      Real.log ‖riemannZeta (horizontalAt t x)‖ =
        (∑ rho ∈ F, (D rho : ℝ) * Real.log ‖horizontalAt t x - rho‖) +
          Real.log ‖g (horizontalAt t x)‖ := by
    filter_upwards [(hbad.image Complex.re).countable.ae_notMem volume] with x hx hxI
    by_contra hn
    apply hx
    exact ⟨horizontalAt t x, ⟨hpoint ht (Set.uIoc_subset_uIcc hxI), hn⟩, by simp [horizontalAt]⟩
  have hiSum : IntervalIntegrable
      (fun x => ∑ rho ∈ F, (D rho : ℝ) * Real.log ‖horizontalAt t x - rho‖) volume a b := by
    convert! IntervalIntegrable.sum F
      (fun rho _ => (log_norm_zero_factor_integrable rho t a b).const_mul (D rho : ℝ)) using 1
    funext x
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_add hiSum
    (hgI t ht), intervalIntegral.integral_finsetSum
      (fun rho _ => (log_norm_zero_factor_integrable rho t a b).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

#print axioms horizontal_zero_log_integral_continuous
#print axioms zeta_finite_horizontal_log_continuousAt

end LiuWang.Proof.Campaign20260915.ZetaWinding
