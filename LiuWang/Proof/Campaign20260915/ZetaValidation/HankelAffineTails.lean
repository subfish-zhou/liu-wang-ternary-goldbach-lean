import LiuWang.Proof.Campaign20260915.ZetaValidation.SourceC2Geometry

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Asymptotics
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsHankelLog_coordinates_bound (z : ℂ) :
    (rsHankelLog z).re = Real.log ‖z‖ ∧ |(rsHankelLog z).im| ≤ 2 * Real.pi := by
  constructor
  · simp [rsHankelLog, log_re]
  · have h := abs_arg_le_pi (-I * z)
    simp only [rsHankelLog, add_im, log_im, mul_im, ofReal_re, ofReal_im,
      I_im, I_re, mul_one, mul_zero, add_zero, div_ofNat, zero_div]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp h).1, Real.pi_pos],
      by linarith [(abs_le.mp h).2, Real.pi_pos]⟩

theorem rsHankelKernel_lower_bound {s z : ℂ} (m : ℕ)
    (hs : s.re ≤ 1) (hz : z.im ≤ -1) :
    ‖rsHankelKernel s m z‖ ≤
      Real.exp (2 * Real.pi * |s.im|) * Real.exp (2 * Real.pi * m * z.im) := by
  have hn : 1 ≤ ‖z‖ := by
    have h := abs_im_le_norm z
    rw [abs_of_neg (by linarith)] at h
    linarith
  have hl := rsHankelLog_coordinates_bound z
  have hfirst : (s.re - 1) * (rsHankelLog z).re ≤ 0 := by
    rw [hl.1]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_nonneg hn)
  have hphase : -s.im * (rsHankelLog z).im ≤ 2 * Real.pi * |s.im| := by
    calc
      _ ≤ |s.im| * |(rsHankelLog z).im| := by
        simpa only [abs_mul, abs_neg] using le_abs_self (-s.im * (rsHankelLog z).im)
      _ ≤ |s.im| * (2 * Real.pi) := mul_le_mul_of_nonneg_left hl.2 (abs_nonneg _)
      _ = _ := by ring
  have hnum : ‖rsHankelNumerator s m z‖ ≤
      Real.exp (2 * Real.pi * |s.im|) * Real.exp (2 * Real.pi * m * z.im) := by
    rw [rsHankelNumerator, norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp [sub_re, mul_re, sub_im, mul_im]
    nlinarith
  have hden : 1 ≤ ‖rsHankelDenominator z‖ := by
    have hnorm := norm_sub_norm_le (exp (2 * Real.pi * I * z)) 1
    have he : 2 ≤ ‖exp (2 * Real.pi * I * z)‖ := by
      rw [norm_exp]
      have hx : 1 ≤ (2 * Real.pi * I * z).re := by
        simp
        nlinarith [Real.two_le_pi]
      linarith [Real.add_one_le_exp (2 * Real.pi * I * z).re]
    simp only [norm_one] at hnorm
    change 1 ≤ ‖exp (2 * Real.pi * I * z) - 1‖
    linarith
  rw [rsHankelKernel, norm_div]
  exact (div_le_self (norm_nonneg _) hden).trans hnum

theorem rsHankel_affine_tail_integrable {s q v : ℂ} {m : ℕ} (hm : 0 < m)
    (hs : s.re ≤ 1) (hv : v.im < 0) (a : ℝ)
    (hc : ContinuousOn (fun y : ℝ => rsHankelKernel s m (q + y * v)) (Ici a)) :
    IntegrableOn (fun y : ℝ => rsHankelKernel s m (q + y * v)) (Ioi a) := by
  have hrate : 2 * Real.pi * (m : ℝ) * v.im < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hv
  have ho : (fun y : ℝ => rsHankelKernel s m (q + y * v)) =O[atTop]
      (fun y : ℝ => Real.exp ((2 * Real.pi * m * v.im) * y)) := by
    apply IsBigO.of_bound (Real.exp (2 * Real.pi * |s.im| + 2 * Real.pi * m * q.im))
    filter_upwards [eventually_ge_atTop ((q.im + 1) / (-v.im))] with y hy
    have hh := (div_le_iff₀ (neg_pos.mpr hv)).mp hy
    have him : (q + y * v).im ≤ -1 := by simp; nlinarith
    have h := rsHankelKernel_lower_bound m hs him
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (h.trans_eq (by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        simp [mul_im]
        ring))
  exact ((hc.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    ho ⟨Ioi a, Ioi_mem_atTop a, integrableOn_exp_mul_Ioi hrate a⟩).mono_set Ioi_subset_Ici_self

end LiuWang.Proof.Campaign20260915.ZetaValidation
