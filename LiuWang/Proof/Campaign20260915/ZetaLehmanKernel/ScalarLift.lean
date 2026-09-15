import LiuWang.Proof.Campaign20260915.ZetaWinding.LogKernel

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaLehmanKernel

open LiuWang.Proof.Campaign20260915.ZetaWinding

def logRadius (y u : ℝ) : ℝ := Real.log ‖(u : ℂ) + (y : ℂ) * I‖

def zeroLoss (a y : ℝ) : ℝ :=
  logNormPrimitive y (a + 2) - 2 * logNormPrimitive y (a + 1) +
    logNormPrimitive y a

def radialMajorant (y u : ℝ) : ℝ :=
  (Real.log u + y ^ 2 * u ^ 2 / 2) / (1 + y ^ 2) ^ 2 -
    Real.log (u ^ 2 + y ^ 2) / 2

theorem radialMajorant_hasDerivAt (y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (radialMajorant y)
      (y ^ 2 * (u ^ 2 - 1) ^ 2 /
        (u * (u ^ 2 + y ^ 2) * (1 + y ^ 2) ^ 2)) u := by
  have hq : u ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hd : 1 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h := (((Real.hasDerivAt_log hu.ne').add
    ((((hasDerivAt_id u).pow 2).const_mul (y ^ 2)).div_const 2)).div_const
      ((1 + y ^ 2) ^ 2)).sub
    (((((hasDerivAt_id u).pow 2).add_const (y ^ 2)).log hq).div_const 2)
  convert! h using 1
  norm_num only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp [hu.ne', hq, hd]
  ring

theorem radialMajorant_monotone (y : ℝ) :
    MonotoneOn (radialMajorant y) (Set.Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
  · intro u hu
    exact (radialMajorant_hasDerivAt y hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (radialMajorant_hasDerivAt y (interior_subset hu)).hasDerivWithinAt
  · intro u hu
    have hp : 0 < u := interior_subset hu
    positivity

theorem logRadius_shift_le (y : ℝ) {u : ℝ} (hu : -(1 / 2 : ℝ) ≤ u)
    (hu0 : u ≠ 0) :
    logRadius y (u + 1) - logRadius y u ≤
      (Real.log (u + 1) - Real.log u + y ^ 2 * (u + 1 / 2)) /
        (1 + y ^ 2) ^ 2 := by
  have hp : 0 < u + 1 := by linarith
  have ha : |u| ≤ u + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hm := radialMajorant_monotone y (abs_pos.mpr hu0) hp ha
  simp only [radialMajorant, Real.log_abs, sq_abs] at hm
  rw [logRadius, logRadius, log_norm_horizontal, log_norm_horizontal]
  have hd : 0 < (1 + y ^ 2) ^ 2 := by positivity
  apply (le_div_iff₀ hd).mpr
  field_simp at hm
  nlinarith

theorem logRadius_integrable (y a b : ℝ) :
    IntervalIntegrable (logRadius y) volume a b :=
  log_norm_horizontal_integrable y a b

theorem logRadius_shift_integrable (y a b : ℝ) :
    IntervalIntegrable (fun u => logRadius y (u + 1)) volume a b := by
  simpa using (logRadius_integrable y (a + 1) (b + 1)).comp_add_right 1

theorem zeroLoss_eq_integral (a y : ℝ) :
    zeroLoss a y = ∫ u in a..(a + 1), logRadius y (u + 1) - logRadius y u := by
  rw [intervalIntegral.integral_sub (logRadius_shift_integrable y a (a + 1))
      (logRadius_integrable y a (a + 1)),
    intervalIntegral.integral_comp_add_right (logRadius y) 1]
  simp only [logRadius, integral_log_norm_horizontal]
  unfold zeroLoss
  rw [show a + 1 + 1 = a + 2 by ring]
  ring

theorem zeroLoss_lift (y : ℝ) {a : ℝ} (ha : -(1 / 2 : ℝ) ≤ a) :
    zeroLoss a y ≤ (zeroLoss a 0 + y ^ 2 * (a + 1)) / (1 + y ^ 2) ^ 2 := by
  have hlog : ∀ u : ℝ, logRadius 0 u = Real.log u := by
    intro u
    simp [logRadius, Real.log_abs]
  have hi : IntervalIntegrable
      (fun u : ℝ => Real.log (u + 1) - Real.log u) volume a (a + 1) := by
    simpa only [← hlog] using
      (logRadius_shift_integrable 0 a (a + 1)).sub (logRadius_integrable 0 a (a + 1))
  have hj : IntervalIntegrable (fun u : ℝ => u + 1 / 2) volume a (a + 1) :=
    (by fun_prop : Continuous (fun u : ℝ => u + 1 / 2)).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_ae_restrict (by linarith : a ≤ a + 1)
    ((logRadius_shift_integrable y a (a + 1)).sub (logRadius_integrable y a (a + 1)))
    ((hi.add (hj.const_mul (y ^ 2))).div_const ((1 + y ^ 2) ^ 2)) ?_
  · rw [← zeroLoss_eq_integral, intervalIntegral.integral_div,
      intervalIntegral.integral_add hi (hj.const_mul (y ^ 2)),
      intervalIntegral.integral_const_mul] at hm
    have he : (∫ u in a..(a + 1), Real.log (u + 1) - Real.log u) = zeroLoss a 0 := by
      rw [zeroLoss_eq_integral]
      simp only [hlog]
    have hx : (∫ u in a..(a + 1), u + (1 / 2 : ℝ)) = a + 1 := by
      rw [intervalIntegral.integral_add (f := fun u : ℝ => u) (g := fun _ => 1 / 2)
          (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
        integral_id, intervalIntegral.integral_const]
      simp
      ring
    rwa [he, hx] at hm
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      (volume.ae_ne (0 : ℝ)).filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)] with u hu hu0
    exact logRadius_shift_le y (by linarith [hu.1]) hu0

#print axioms zeroLoss_lift

end LiuWang.Proof.Campaign20260915.ZetaLehmanKernel
