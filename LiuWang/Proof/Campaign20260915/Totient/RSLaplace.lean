import LiuWang.Proof.Campaign20260915.Totient.RSZeroRegion
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.Totient

def rsLaplace (m c b u : ℝ) : ℝ := Real.exp (-m * u - c / u) * (u - b)

def rsLaplacePrimitive (m c b u : ℝ) : ℝ :=
  Real.exp (-m * u - c / u) * ((u - b) / m + 1 / m ^ 2)

def rsLaplaceCorrection (m c b u : ℝ) : ℝ :=
  c / (m * u ^ 2) * (1 + 1 / (m * (u - b)))

theorem rsLaplacePrimitive_deriv {m c b u : ℝ} (hm : 0 < m) (hu : 0 < u)
    (hb : b < u) :
    HasDerivAt (rsLaplacePrimitive m c b)
      (-(1 - rsLaplaceCorrection m c b u) * rsLaplace m c b u) u := by
  have hlin : HasDerivAt (fun v : ℝ => -m * v - c / v) (-m + c / u ^ 2) u := by
    convert! ((hasDerivAt_id u).const_mul (-m)).sub
      ((hasDerivAt_const u c).div (hasDerivAt_id u) hu.ne') using 1
    simp only [id_eq]
    ring
  have hfac : HasDerivAt (fun v : ℝ => (v - b) / m + 1 / m ^ 2) (1 / m) u := by
    simpa only [id_eq] using!
      (((hasDerivAt_id u).sub_const b).div_const m).add_const (1 / m ^ 2)
  convert! hlin.exp.mul hfac using 1
  dsimp [rsLaplacePrimitive, rsLaplaceCorrection, rsLaplace]
  field_simp [sub_ne_zero.mpr hb.ne']
  ring

theorem rsLaplaceCorrection_antitone {m c b v u : ℝ} (hm : 0 < m) (hc : 0 ≤ c)
    (hv : 0 < v) (hb : b < v) (hvu : v ≤ u) :
    rsLaplaceCorrection m c b u ≤ rsLaplaceCorrection m c b v := by
  have hu : 0 < u := hv.trans_le hvu
  have hub : 0 < u - b := by linarith
  have hvb : 0 < v - b := by linarith
  unfold rsLaplaceCorrection
  apply mul_le_mul
  · apply div_le_div_of_nonneg_left hc (by positivity)
    gcongr
  · apply add_le_add_right
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  · positivity
  · positivity

theorem rsLaplacePrimitive_tendsto {m c b : ℝ} (hm : 0 < m) :
    Tendsto (rsLaplacePrimitive m c b) atTop (𝓝 0) := by
  have hc : Tendsto (fun u : ℝ => Real.exp (-c / u)) atTop (𝓝 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := -c)).mul
        (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0)))
    simpa only [mul_zero, Real.exp_zero, div_eq_mul_inv, Function.comp_def] using! h
  have h0 : Tendsto (fun u : ℝ => Real.exp (-m * u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have h1 : Tendsto (fun u : ℝ => u * Real.exp (-m * u)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) m hm
  have h := ((h1.div_const m).add (h0.mul_const (-b / m + 1 / m ^ 2))).mul hc
  convert! h using 1
  · ext u
    dsimp [rsLaplacePrimitive]
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  · simp

theorem rsLaplace_integral_le {m c b v : ℝ} (hm : 0 < m) (hc : 0 ≤ c)
    (hv : 0 < v) (hb : b < v) (hr : rsLaplaceCorrection m c b v < 1) :
    IntegrableOn (rsLaplace m c b) (Ioi v) ∧
      (∫ u in Ioi v, rsLaplace m c b u) ≤
        rsLaplacePrimitive m c b v / (1 - rsLaplaceCorrection m c b v) := by
  let f := rsLaplacePrimitive m c b
  let g := fun u => (1 - rsLaplaceCorrection m c b u) * rsLaplace m c b u
  let D := 1 - rsLaplaceCorrection m c b v
  have hD : 0 < D := by dsimp [D]; linarith
  have hder (u : ℝ) (hu : u ∈ Ici v) : HasDerivAt (fun t => -f t) (g u) u := by
    have h := (rsLaplacePrimitive_deriv (c := c) hm (hv.trans_le hu) (hb.trans_le hu)).neg
    simpa only [neg_mul, neg_neg, Pi.neg_apply] using! h
  have hnon (u : ℝ) (hu : u ∈ Ioi v) : 0 ≤ g u := by
    have ht := rsLaplaceCorrection_antitone hm hc hv hb hu.le
    have hl : 0 ≤ rsLaplace m c b u := by
      unfold rsLaplace
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hb.le.trans hu.le))
    dsimp [g]
    exact mul_nonneg (by linarith) hl
  have ht : Tendsto (fun t => -f t) atTop (𝓝 0) := by
    simpa only [neg_zero] using (rsLaplacePrimitive_tendsto (c := c) (b := b) hm).neg
  have hi := integrableOn_Ioi_deriv_of_nonneg' hder hnon ht
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hder hnon ht
  simp only [sub_neg_eq_add, zero_add] at he
  have hbound (u : ℝ) (hu : u ∈ Ioi v) :
      ‖rsLaplace m c b u‖ ≤ g u / D := by
    have ht := rsLaplaceCorrection_antitone hm hc hv hb hu.le
    have hl : 0 ≤ rsLaplace m c b u := by
      unfold rsLaplace
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hb.le.trans hu.le))
    rw [Real.norm_eq_abs, abs_of_nonneg hl]
    apply (le_div_iff₀ hD).mpr
    dsimp [D, g]
    nlinarith only [mul_le_mul_of_nonneg_right ht hl]
  have hmeas : AEStronglyMeasurable (rsLaplace m c b) (volume.restrict (Ioi v)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hv.trans hu)
    unfold rsLaplace
    fun_prop
  have hli : IntegrableOn (rsLaplace m c b) (Ioi v) :=
    (hi.div_const D).mono' hmeas (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  refine ⟨hli, ?_⟩
  have h := integral_mono_ae hli (hi.div_const D)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound u hu))
  rw [integral_div, he] at h
  exact h

#print axioms rsLaplace_integral_le

end LiuWang.Proof.Campaign20260915.Totient
