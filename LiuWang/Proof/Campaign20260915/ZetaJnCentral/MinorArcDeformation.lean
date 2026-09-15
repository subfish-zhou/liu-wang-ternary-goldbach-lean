import LiuWang.Proof.Campaign20260915.ZetaJnCentral.MinorArcGeometry
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Complex.HasPrimitives

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Metric

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

def sourcePoleCap (eta : ℝ) (k : ℤ) (e : ℝ) : Set ℂ :=
  (ball (eta : ℂ) eta ∩ ball (k : ℂ) (1 / 2)) ∩
    {z : ℂ | e * (k : ℝ) < e * (z.re + z.im)}

theorem sourcePoleCap_open (eta : ℝ) (k : ℤ) (e : ℝ) :
    IsOpen (sourcePoleCap eta k e) := by
  exact (isOpen_ball.inter isOpen_ball).inter (isOpen_lt continuous_const (by fun_prop))

theorem sourcePoleCap_convex (eta : ℝ) (k : ℤ) (e : ℝ) :
    Convex ℝ (sourcePoleCap eta k e) := by
  let L : ℂ →ₗ[ℝ] ℝ := e • (reCLM.toLinearMap + imCLM.toLinearMap)
  exact ((convex_ball (eta : ℂ) eta).inter (convex_ball (k : ℂ) (1 / 2))).inter
    (convex_halfSpace_gt ⟨L.map_add, L.map_smul⟩ (e * k))

theorem sourcePoleCap_no_integer {eta e : ℝ} {k : ℤ} {z : ℂ}
    (hz : z ∈ sourcePoleCap eta k e) : ¬∃ n : ℤ, z = n := by
  rintro ⟨n, rfl⟩
  have hn : |(n : ℝ) - k| < 1 / 2 := by
    simpa only [mem_ball, dist_eq_norm, ← ofReal_intCast, ← ofReal_sub,
      norm_real, Real.norm_eq_abs] using hz.1.2
  have hl : (-1 : ℝ) < (n : ℝ) - k := by linarith [(abs_lt.mp hn).1]
  have hr : (n : ℝ) - k < 1 := by linarith [(abs_lt.mp hn).2]
  have hl' : (-1 : ℤ) < n - k := by exact_mod_cast hl
  have hr' : n - k < (1 : ℤ) := by exact_mod_cast hr
  have hnk : n = k := by omega
  have hh := hz.2
  simp only [mem_ofPred_eq, hnk, intCast_re, intCast_im, add_zero, lt_self_iff_false] at hh

theorem sourcePoleCap_analytic (sigma : ℝ) (m N : ℕ) {eta e : ℝ} {k : ℤ}
    (he : 0 < eta) {z : ℂ} (hz : z ∈ sourcePoleCap eta k e) :
    AnalyticAt ℂ (jnCore sigma eta m N) z := by
  exact jnCore_analytic sigma m N he
    (by simpa only [mem_ball, dist_eq_norm] using hz.1.1)
    (mt (rsHankelDenominator_zero_iff z).mp (sourcePoleCap_no_integer hz))

theorem sourcePoleCap_exact (sigma : ℝ) (m N : ℕ) {eta : ℝ} (he : 0 < eta)
    (k : ℤ) (e : ℝ) : IsExactOn (jnCore sigma eta m N) (sourcePoleCap eta k e) := by
  have hf : DifferentiableOn ℂ (jnCore sigma eta m N) (sourcePoleCap eta k e) :=
    fun z hz => (sourcePoleCap_analytic sigma m N he hz).differentiableAt.differentiableWithinAt
  obtain ⟨g, hg⟩ := (sourcePoleCap_convex eta k e).exists_forall_hasDerivWithinAt hf
  exact ⟨g, fun z hz => (hg z hz).hasDerivAt ((sourcePoleCap_open eta k e).mem_nhds hz)⟩

theorem sourcePoleCap_minor {eta e : ℝ} {k : ℤ}
    (hD : sourcePoleDistance < eta) (he : |e| = 1)
    (hside : 0 < e * (eta - k)) (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    {theta : ℝ} (ht : theta ∈ Icc (-sourceMinorAngle eta k e) (sourceMinorAngle eta k e)) :
    sourceMinorPoint k e theta ∈ sourcePoleCap eta k e := by
  refine ⟨⟨?_, ?_⟩, sourceMinorPoint_side he hside hk ht⟩
  · rw [mem_ball, dist_eq_norm]
    exact (sourceMinorPoint_distance he hk theta).trans_lt hD
  · rw [mem_ball, dist_eq_norm]
    rw [sourceMinorPoint_radius k he theta]
    exact sourcePoleRadius_lt_half

def descentAffine (eta : ℝ) : ℝ →ᵃ[ℝ] ℂ where
  toFun := rsDescentPoint eta
  linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight rsDescentDirection
  map_vadd' p v := by
    simp [rsDescentPoint]
    ring

theorem sourcePoleCap_minor_chord {eta e : ℝ} {k : ℤ}
    (hD : sourcePoleDistance < eta) (he : |e| = 1)
    (hside : 0 < e * (eta - k)) (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    {y : ℝ} (hy : y ∈ uIcc
      (sourceMinorY eta k e (-sourceMinorAngle eta k e))
      (sourceMinorY eta k e (sourceMinorAngle eta k e))) :
    rsDescentPoint eta y ∈ sourcePoleCap eta k e := by
  have hc := (sourcePoleCap_convex eta k e).affine_preimage (descentAffine eta)
  have ha := (sourceMinorAngle_mem he hside hk).1
  have hl := sourcePoleCap_minor hD he hside hk (theta := -sourceMinorAngle eta k e)
    ⟨le_rfl, by linarith⟩
  have hr := sourcePoleCap_minor hD he hside hk (theta := sourceMinorAngle eta k e)
    ⟨by linarith, le_rfl⟩
  rw [sourceMinorPoint_endpoint he hside hk (Or.inr rfl)] at hl
  rw [sourceMinorPoint_endpoint he hside hk (Or.inl rfl)] at hr
  exact hc.ordConnected.uIcc_subset hl hr hy

def jnSourceMinorArc (sigma eta : ℝ) (m N : ℕ) (k : ℤ) (e : ℝ) : ℂ :=
  ∫ theta : ℝ in (-sourceMinorAngle eta k e)..(sourceMinorAngle eta k e),
    sourceMinorVelocity e theta * jnCore sigma eta m N (sourceMinorPoint k e theta)

theorem sourcePoleCap_path_integral (sigma : ℝ) (m N : ℕ) {eta e a b : ℝ} {k : ℤ}
    (he : 0 < eta) {g : ℂ → ℂ}
    (hg : ∀ z ∈ sourcePoleCap eta k e, HasDerivAt g (jnCore sigma eta m N z) z)
    {gamma delta : ℝ → ℂ}
    (hgamma : ∀ t ∈ uIcc a b, gamma t ∈ sourcePoleCap eta k e)
    (hd : ∀ t ∈ uIcc a b, HasDerivAt gamma (delta t) t)
    (hc : ContinuousOn delta (uIcc a b)) :
    (∫ t : ℝ in a..b, delta t * jnCore sigma eta m N (gamma t)) =
      g (gamma b) - g (gamma a) := by
  have hf : ContinuousOn (fun t => jnCore sigma eta m N (gamma t)) (uIcc a b) := by
    intro t ht
    exact ((sourcePoleCap_analytic sigma m N he (hgamma t ht)).continuousAt.comp
      (hd t ht).continuousAt).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => g (gamma t))
    (f' := fun t : ℝ => delta t * jnCore sigma eta m N (gamma t)) _ (hc.mul hf).intervalIntegrable
  intro t ht
  simpa only [Function.comp_def, smul_eq_mul] using (hg _ (hgamma t ht)).scomp t (hd t ht)

theorem jn_source_minor_deformation (sigma : ℝ) (m N : ℕ) {eta e : ℝ} {k : ℤ}
    (heta : 0 < eta) (hD : sourcePoleDistance < eta) (he : |e| = 1)
    (hside : 0 < e * (eta - k)) (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) :
    (∫ y : ℝ in (sourceMinorY eta k e (-sourceMinorAngle eta k e))..
        (sourceMinorY eta k e (sourceMinorAngle eta k e)), rsJnIntegrand sigma eta m N y) =
      jnSourceMinorArc sigma eta m N k e := by
  obtain ⟨g, hg⟩ := sourcePoleCap_exact sigma m N heta k e
  have hl := sourcePoleCap_path_integral sigma m N heta hg
    (gamma := rsDescentPoint eta) (delta := fun _ => rsDescentDirection)
    (fun _ hy => sourcePoleCap_minor_chord hD he hside hk hy)
    (fun y _ => by
      unfold rsDescentPoint
      simpa using
        ((ofRealCLM.hasDerivAt (x := y)).const_mul rsDescentDirection).const_add (eta : ℂ))
    continuousOn_const
  have ha := (sourceMinorAngle_mem he hside hk).1
  have hr := sourcePoleCap_path_integral sigma m N heta hg
    (gamma := sourceMinorPoint k e) (delta := sourceMinorVelocity e)
    (a := -sourceMinorAngle eta k e) (b := sourceMinorAngle eta k e)
    (fun theta ht => sourcePoleCap_minor hD he hside hk (by
      rwa [uIcc_of_le (by linarith : -sourceMinorAngle eta k e ≤ sourceMinorAngle eta k e)] at ht))
    (fun theta _ => sourceMinorPoint_deriv k e theta)
    (by unfold sourceMinorVelocity; fun_prop)
  simp only [jnCore_descent] at hl
  rw [sourceMinorPoint_endpoint he hside hk (Or.inl rfl),
    sourceMinorPoint_endpoint he hside hk (Or.inr rfl)] at hr
  exact hl.trans hr.symm

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
