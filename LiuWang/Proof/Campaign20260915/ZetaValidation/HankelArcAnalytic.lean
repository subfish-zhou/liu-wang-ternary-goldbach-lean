import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelTailAnalytic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped Topology Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsHankelLift_parameter_deriv (s w : ℂ) (m : ℕ) :
    HasDerivAt (fun q : ℂ => rsHankelLift q m w) (w * rsHankelLift s m w) s := by
  have h := ((((hasDerivAt_id s).mul_const w).sub_const
    (2 * Real.pi * I * m * exp w)).cexp).div_const (rsHankelDenominator (exp w))
  simp only [id_eq, one_mul] at h
  change HasDerivAt (fun q : ℂ => rsHankelLift q m w)
    (exp (s * w - 2 * Real.pi * I * m * exp w) * w /
      rsHankelDenominator (exp w)) s at h
  have he : exp (s * w - 2 * Real.pi * I * m * exp w) * w /
      rsHankelDenominator (exp w) = w * rsHankelLift s m w := by
    unfold rsHankelLift
    ring
  rwa [he] at h

theorem rsHankelLift_joint_continuous (m : ℕ) {u : ℝ} (hu : u < 0) :
    Continuous (fun p : ℂ × ℝ => rsHankelLift p.1 m (u + p.2 * I)) := by
  unfold rsHankelLift
  apply Continuous.div (by fun_prop)
    (by unfold rsHankelDenominator; fun_prop)
  intro p
  apply rsHankelDenominator_ne_zero_of_norm (exp_ne_zero _)
  simpa [norm_exp] using Real.exp_lt_one_iff.mpr hu

theorem rsHankelArc_parameter_deriv (m : ℕ) {u : ℝ} (hu : u < 0) (s : ℂ) :
    HasDerivAt (fun q : ℂ => rsHankelArc q m u)
      (I * ∫ θ : ℝ in -(Real.pi / 2)..3 * Real.pi / 2,
        (u + θ * I) * rsHankelLift s m (u + θ * I)) s := by
  let F (q : ℂ) (θ : ℝ) := rsHankelLift q m (u + θ * I)
  let D (q : ℂ) (θ : ℝ) := (u + θ * I) * rsHankelLift q m (u + θ * I)
  have hF := rsHankelLift_joint_continuous m hu
  have hD : Continuous (fun p : ℂ × ℝ => D p.1 p.2) :=
    (show Continuous (fun p : ℂ × ℝ => (u : ℂ) + p.2 * I) by fun_prop).mul hF
  have hFc (q : ℂ) : Continuous (F q) :=
    hF.comp (show Continuous (fun θ : ℝ => (q, θ)) by fun_prop)
  have hDc (q : ℂ) : Continuous (D q) :=
    hD.comp (show Continuous (fun θ : ℝ => (q, θ)) by fun_prop)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s 1).prod
    (isCompact_Icc (a := -(Real.pi / 2)) (b := 3 * Real.pi / 2))).exists_bound_of_continuousOn
      hD.continuousOn
  have hbound : ∀ᵐ θ : ℝ, θ ∈ Ι (-(Real.pi / 2)) (3 * Real.pi / 2) →
      ∀ q ∈ ball s 1, ‖D q θ‖ ≤ C := by
    apply ae_of_all
    intro θ hθ q hq
    apply hC (q, θ)
    refine ⟨ball_subset_closedBall hq, ?_⟩
    simpa [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 3 * Real.pi / 2)]
      using uIoc_subset_uIcc hθ
  have hderiv : ∀ᵐ θ : ℝ, θ ∈ Ι (-(Real.pi / 2)) (3 * Real.pi / 2) →
      ∀ q ∈ ball s 1, HasDerivAt (fun q => F q θ) (D q θ) q :=
    ae_of_all _ (fun θ _ q _ => rsHankelLift_parameter_deriv q _ m)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (bound := fun _ => C)
    (ball_mem_nhds s (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun q => (hFc q).aestronglyMeasurable.restrict))
    (hFc s |>.intervalIntegrable _ _) ((hDc s).aestronglyMeasurable.restrict)
    hbound intervalIntegrable_const hderiv
  exact h.2.const_mul I

theorem rsHankelC1_differentiable {m : ℕ} (hm : 0 < m) {u : ℝ} (hu : u < 0) :
    Differentiable ℂ (fun s : ℂ => rsHankelC1 s m u) := by
  obtain ⟨hr, hl⟩ := rsHankelBank_tail_differentiable hm (Real.exp_pos u)
  have ha : Differentiable ℂ (fun s : ℂ => rsHankelArc s m u) :=
    fun s => (rsHankelArc_parameter_deriv m hu s).differentiableAt
  exact (ha.add hl).sub hr

end LiuWang.Proof.Campaign20260915.ZetaValidation
