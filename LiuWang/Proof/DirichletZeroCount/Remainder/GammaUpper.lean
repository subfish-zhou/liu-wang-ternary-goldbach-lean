import LiuWang.Proof.DirichletZeroCount.Remainder.Trapezoid

/-! # A nonpositive imaginary Stirling remainder throughout the first quadrant -/

set_option autoImplicit false
noncomputable section
open Complex Filter MeasureTheory
open scoped Topology Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem phaseTail_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (phaseTail z) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [ofReal_inv, ofReal_natCast, ofReal_zero, Function.comp_def, Pi.inv_apply] using
      (continuous_ofReal.tendsto _).comp
        (Tendsto.inv_tendsto_atTop (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hg : Tendsto (fun n : ℕ => z / (n : ℂ)) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have hlog : Tendsto (fun n : ℕ => log (1 + z / (n : ℂ))) atTop (𝓝 0) := by
    have hone : Tendsto (fun n : ℕ => 1 + z / (n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℂ))).add hg
    have h := ((hasDerivAt_log (by simp : (1 : ℂ) ∈ slitPlane)).continuousAt).tendsto.comp
      hone
    simpa only [Function.comp_def, log_one] using h
  have hng : Tendsto (fun n : ℕ => (n : ℂ) * (z / (n : ℂ))) atTop (𝓝 z) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  have hnl := tendsto_nat_mul_log_one_add_of_tendsto hng
  have hlim : Tendsto (fun n : ℕ =>
      (z - ((z + 1 / 2) * log (1 + z / (n : ℂ)) +
        (n : ℂ) * log (1 + z / (n : ℂ)))).im) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, zero_add, sub_self, zero_im] using
      (continuous_im.tendsto _).comp
      ((tendsto_const_nhds (x := z)).sub
        (((tendsto_const_nhds (x := z + 1 / 2)).mul hlog).add hnl))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hzn : z + n ≠ 0 := by
    intro h
    have hp : 0 < (z + n).re := by simp only [add_re, natCast_re]; linarith
    simp [h] at hp
  have hfactor : (n : ℂ) * (1 + z / (n : ℂ)) = z + n := by field_simp; ring
  have hsmall : 1 + z / (n : ℂ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfactor
    exact hzn hfactor.symm
  have he : log (z + n) = (Real.log n : ℂ) + log (1 + z / (n : ℂ)) := by
    rw [← hfactor]
    exact log_ofReal_mul hnR hsmall
  dsimp [phaseTail]
  rw [he]
  simp only [add_im, mul_im, ofReal_re, ofReal_im, natCast_re, natCast_im]
  norm_num
  simp only [log_re, Complex.norm_natCast]
  ring

theorem logGamma_im_le_stirling {z : ℂ} (hz : 0 < z.re) (ht : 0 ≤ z.im) :
    (logGamma z).im ≤ stirlingPhase z := by
  have hleft := (continuous_im.tendsto _).comp (logGamma_tendsto hz)
  have hright := (tendsto_const_nhds (x := stirlingPhase z)).add (phaseTail_tendsto hz)
  simpa only [add_zero] using le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall (logGammaSeq_im_le hz ht))

def gammaPhaseMain (a H : ℝ) : ℝ :=
  2 * stirlingPhase (((a : ℂ) + (H : ℂ) * I) / 2)

theorem digammaVertical_le_main {a H : ℝ} (ha : 0 < a) (hH : 0 ≤ H) :
    Argument.digammaVertical a H ≤ gammaPhaseMain a H := by
  rw [digammaVertical_eq_logGamma ha]
  exact mul_le_mul_of_nonneg_left
    (logGamma_im_le_stirling (by simpa using half_pos ha) (by simpa using div_nonneg hH (by norm_num : (0 : ℝ) ≤ 2)))
    (by norm_num)

theorem gammaPhaseMain_zero (a : ℝ) (ha : 0 < a) : gammaPhaseMain a 0 = 0 := by
  simp only [gammaPhaseMain, stirlingPhase, ofReal_zero, zero_mul, add_zero]
  rw [← ofReal_ofNat, ← ofReal_div, ← ofReal_log (by positivity : 0 ≤ a / 2)]
  simp

theorem gammaPhaseMain_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (gammaPhaseMain a) := by
  have hs (H : ℝ) : (((a : ℂ) + (H : ℂ) * I) / 2) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa using half_pos ha
  have hc : Continuous (fun H : ℝ => log (((a : ℂ) + (H : ℂ) * I) / 2)) :=
    continuous_iff_continuousAt.mpr fun H => ((hasDerivAt_log (hs H)).continuousAt).comp
      (f := fun t : ℝ => ((a : ℂ) + (t : ℂ) * I) / 2) (by fun_prop)
  unfold gammaPhaseMain stirlingPhase
  have hlin : Continuous (fun H : ℝ => ((a : ℂ) + (H : ℂ) * I) / 2) := by fun_prop
  exact continuous_const.mul (continuous_im.comp (((hlin.sub continuous_const).mul hc).sub hlin))

theorem completed_count_le_gamma_main {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    (count chi 0 H : ℝ) ≤
      (H * Real.log ((q : ℝ) / Real.pi) +
        (Argument.rightThreeIntegral (logDeriv chi.LFunction) b H).im +
        (if chi.Even then gammaPhaseMain (1 / 2) H else gammaPhaseMain (3 / 2) H)) / Real.pi := by
  rw [Argument.completed_count_digamma hchi hprim hb hH hreg]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  apply add_le_add_right
  split_ifs
  · exact digammaVertical_le_main (by norm_num) hH
  · exact digammaVertical_le_main (by norm_num) hH

end LiuWang.Proof.DirichletZeroCount.Remainder
