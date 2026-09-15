import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Rational

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate

def refinedBound (u v : ℝ) : ℝ :=
  (v - u) / 4 * cellMass u v *
    (Real.exp (cellPhase u v u) + 2 * Real.exp (cellPhase u v ((u + v) / 2)) +
      Real.exp (cellPhase u v v))

def rationalRefined (u v : ℚ) : ℚ :=
  (v - u) / 4 * qMass u v *
    (expUpperQ (-qPhase u v u) + 2 * expUpperQ (-qPhase u v ((u + v) / 2)) +
      expUpperQ (-qPhase u v v))

theorem affine_exp_integral_upper (c k m : ℝ) {a b : ℝ} (hab : a < b) :
    (∫ s in a..b, Real.exp (c + k * (s - m))) ≤
      (b - a) / 2 * (Real.exp (c + k * (a - m)) + Real.exp (c + k * (b - m))) := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hp (s : ℝ) (hs : s ∈ Set.Icc a b) :
      Real.exp (c + k * (s - m)) ≤
        chord a b (Real.exp (c + k * (a - m))) (Real.exp (c + k * (b - m))) s := by
    have hw : (b - s) / (b - a) + (s - a) / (b - a) = 1 := by field_simp; ring
    have h := convexOn_exp.2 (Set.mem_univ (c + k * (a - m)))
      (Set.mem_univ (c + k * (b - m)))
      (div_nonneg (sub_nonneg.mpr hs.2) hd.le)
      (div_nonneg (sub_nonneg.mpr hs.1) hd.le) hw
    have he : (b - s) / (b - a) * (c + k * (a - m)) +
        (s - a) / (b - a) * (c + k * (b - m)) = c + k * (s - m) := by
      field_simp
      ring
    simpa only [smul_eq_mul, he, chord] using h
  have hi := intervalIntegral.integral_mono_on hab.le
    ((show Continuous (fun s => Real.exp (c + k * (s - m))) by fun_prop).intervalIntegrable _ _)
    (chord_integrable a b _ _) hp
  rw [integral_chord hab] at hi
  exact hi.trans_eq (by ring)

theorem cell_integral_refined {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v ≤ 100) :
    (∫ s in u..v, integrand 3100 s) ≤ refinedBound u v := by
  have hb : v ≤ 18 * Real.log (3100 : ℝ) := by linarith [log_3100_bounds.1]
  have hden : 0 < 3100 - 4 * v := by linarith
  have hmid : u < (u + v) / 2 ∧ (u + v) / 2 < v := by constructor <;> linarith
  have hM : 0 ≤ cellMass u v := by
    unfold cellMass coeffA coeffB
    have : 0 < (u + v) / 2 := by linarith
    positivity
  have hc : Continuous (fun s => Real.exp (cellPhase u v s)) := by
    unfold cellPhase
    fun_prop
  have h := intervalIntegral.integral_mono_on huv.le
    (integrand_integrable (by norm_num) hu huv.le hb)
    ((hc.const_mul (cellMass u v)).intervalIntegrable _ _)
    (fun s hs => cell_pointwise hu huv hv hs)
  rw [intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable u ((u + v) / 2)) (hc.intervalIntegrable ((u + v) / 2) v)] at h
  have h1 := affine_exp_integral_upper (phase 1481.8 ((u + v) / 2))
    (cellSlope u v) ((u + v) / 2) hmid.1
  have h2 := affine_exp_integral_upper (phase 1481.8 ((u + v) / 2))
    (cellSlope u v) ((u + v) / 2) hmid.2
  have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hM
  exact h.trans (hh.trans_eq (by unfold refinedBound cellPhase; ring))

theorem refined_le_rational {u v : ℚ} (hu : 0 < u) (huv : u < v) (hv : v ≤ 100)
    (hpu : qPhase u v u ≤ 0) (hpm : qPhase u v ((u + v) / 2) ≤ 0)
    (hpv : qPhase u v v ≤ 0) :
    (∫ s in (u : ℝ)..(v : ℝ), integrand 3100 s) ≤ (rationalRefined u v : ℝ) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have hvR : (v : ℝ) ≤ 100 := by exact_mod_cast hv
  have h1 := exp_upperQ (neg_nonneg.mpr hpu)
  have h2 := exp_upperQ (neg_nonneg.mpr hpm)
  have h3 := exp_upperQ (neg_nonneg.mpr hpv)
  simp only [Rat.cast_neg, neg_neg, cast_qPhase] at h1 h2 h3
  push_cast at h2
  apply (cell_integral_refined huR huvR hvR).trans
  unfold refinedBound rationalRefined
  push_cast
  rw [cast_qMass]
  apply mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))) h3)
  have hd : 0 < 3100 - 4 * (v : ℝ) := by linarith
  have hm : 0 < ((u : ℝ) + v) / 2 := by linarith
  unfold cellMass coeffA coeffB
  positivity

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate
