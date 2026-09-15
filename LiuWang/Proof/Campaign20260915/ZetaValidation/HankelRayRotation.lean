import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelLowerSectors
import Mathlib.MeasureTheory.Integral.Asymptotics

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Asymptotics
open scoped Topology Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsHankelRay (s : ℂ) (m : ℕ) (u θ : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi u, rsHankelLift s m (x + θ * I)

theorem rsHankelRay_continuous (s : ℂ) (m : ℕ) {θ : ℝ} (hθ : Real.sin θ < 0) :
    Continuous (fun x : ℝ => rsHankelLift s m (x + θ * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (rsHankelLift_analytic_lower s m (by simpa using hθ)).continuousAt.comp (by fun_prop)

theorem rsHankelRay_integrable {m : ℕ} (hm : 0 < m) (s : ℂ) (u : ℝ) {θ : ℝ}
    (hθ : Real.sin θ ≤ -(1 / 2)) :
    IntegrableOn (fun x : ℝ => rsHankelLift s m (x + θ * I)) (Ioi u) := by
  have hc := rsHankelRay_continuous s m (by linarith : Real.sin θ < 0)
  have ht := rsHankelSector_majorant_tendsto hm (s + 1) |θ|
  have ho : (fun x : ℝ => rsHankelLift s m (x + θ * I)) =O[atTop]
      (fun x : ℝ => Real.exp (-x)) := by
    apply isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hk
    simp only [add_re, one_re, add_im, one_im, add_zero] at hk
    have hn := rsHankelLift_sector_bound s m hx hθ (le_refl |θ|)
    have he : (Real.exp (|s.im| * |θ|) * (Real.exp x) ^ s.re *
        Real.exp (-(Real.pi * m) * Real.exp x)) * Real.exp x =
        Real.exp (|s.im| * |θ|) * (Real.exp x) ^ (s.re + 1) *
          Real.exp (-(Real.pi * m) * Real.exp x) := by
      rw [Real.rpow_add (Real.exp_pos _), Real.rpow_one]
      ring
    have hn' := (mul_le_mul_of_nonneg_right hn (Real.exp_pos x).le).trans (he ▸ hk)
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_neg]
    rw [← one_div]
    exact (le_div_iff₀ (Real.exp_pos x)).mpr hn'
  exact ((hc.continuousOn.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    ho ⟨Ioi u, Ioi_mem_atTop u, integrableOn_exp_neg_Ioi u⟩).mono_set Ioi_subset_Ici_self

theorem rsHankelSector_rectangle (s : ℂ) (m : ℕ) (u v : ℝ) {a b : ℝ}
    (hθ : ∀ θ ∈ uIcc a b, Real.sin θ < 0) :
    rsHankelArcBetween s m v a b - rsHankelArcBetween s m u a b =
      (∫ x : ℝ in u..v, rsHankelLift s m (x + b * I)) -
        ∫ x : ℝ in u..v, rsHankelLift s m (x + a * I) := by
  have hd : DifferentiableOn ℂ (rsHankelLift s m) ([[u, v]] ×ℂ [[a, b]]) := by
    intro w hw
    exact (rsHankelLift_analytic_lower s m (hθ w.im hw.2)).differentiableAt.differentiableWithinAt
  have h := integral_boundary_rect_eq_zero_of_differentiableOn (rsHankelLift s m)
    (u + a * I) (v + b * I) (by simpa using hd)
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_self, add_zero, add_im, mul_im, mul_one, zero_add, smul_eq_mul] at h
  unfold rsHankelArcBetween
  linear_combination h

theorem rsHankelRay_rotation {m : ℕ} (hm : 0 < m) (s : ℂ) (u : ℝ) {a b : ℝ}
    (hθ : ∀ θ ∈ uIcc a b, Real.sin θ ≤ -(1 / 2)) :
    rsHankelRay s m u a = rsHankelArcBetween s m u a b + rsHankelRay s m u b := by
  have ha := rsHankelRay_integrable hm s u (hθ a (left_mem_uIcc))
  have hb := rsHankelRay_integrable hm s u (hθ b (right_mem_uIcc))
  have hta := intervalIntegral_tendsto_integral_Ioi u ha tendsto_id
  have htb := intervalIntegral_tendsto_integral_Ioi u hb tendsto_id
  have hleft := (rsHankelArcBetween_tendsto_zero hm s hθ).sub_const (rsHankelArcBetween s m u a b)
  have he : (fun v : ℝ => rsHankelArcBetween s m v a b - rsHankelArcBetween s m u a b) =
      (fun v => (∫ x : ℝ in u..v, rsHankelLift s m (x + b * I)) -
        ∫ x : ℝ in u..v, rsHankelLift s m (x + a * I)) := by
    funext v
    exact rsHankelSector_rectangle s m u v (fun θ h => lt_of_le_of_lt (hθ θ h) (by norm_num))
  rw [he] at hleft
  have h := tendsto_nhds_unique hleft (htb.sub hta)
  change 0 - rsHankelArcBetween s m u a b = rsHankelRay s m u b - rsHankelRay s m u a at h
  linear_combination h

theorem rsHankelRay_actual (s : ℂ) (m : ℕ) (u : ℝ) {θ : ℝ}
    (hlo : -(Real.pi / 2) < θ) (hhi : θ < 3 * Real.pi / 2) :
    rsHankelRay s m u θ =
      ∫ x : ℝ in Ioi u, exp (x + θ * I) * rsHankelKernel s m (exp (x + θ * I)) := by
  unfold rsHankelRay
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  exact rsHankelLift_actual s m (by simpa using hlo) (by simpa using hhi)

end LiuWang.Proof.Campaign20260915.ZetaValidation
