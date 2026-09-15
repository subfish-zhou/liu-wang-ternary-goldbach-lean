import LiuWang.Proof.Campaign20260915.ZetaMordell.PoleFreeGaussian

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter Set
open scoped Real Topology

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

theorem poleFreeKernel_vertical_tendsto {ι : Type*} {l : Filter ι} {T : ι → ℝ}
    (n : ℕ) (b : ℂ) {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1)
    (hT : Tendsto (fun i => |T i|) l atTop) :
    Tendsto (fun i => ∫ y in u..v, poleFreeKernel n b ((T i : ℂ) + y * I)) l (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := poleFreeKernel_tail_bound n b
  have hg : Tendsto (fun i => Real.exp (-Real.pi / 32 * T i ^ 2)) l (𝓝 0) := by
    have hsq := (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hT
    have hx := Real.tendsto_exp_atBot.comp
      (hsq.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos] : -Real.pi / 32 < 0))
    simpa only [sq_abs, Function.comp_def] using hx
  have hb : Tendsto (fun i => B * Real.exp (-Real.pi / 32 * T i ^ 2) * |v - u|)
      l (𝓝 0) := by simpa using (hg.const_mul B).mul_const |v - u|
  apply squeeze_zero_norm' _ hb
  filter_upwards [hT.eventually (eventually_ge_atTop 3)] with i hi
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y hy
  have hy' := uIoc_subset_uIcc hy
  have hu' := abs_lt.mp hu
  have hv' := abs_lt.mp hv
  have hmin : -1 < min u v := lt_min hu'.1 hv'.1
  have hmax : max u v < 1 := max_lt hu'.2 hv'.2
  exact hB _ _ hi (abs_le.mpr ⟨by linarith [hy'.1], by linarith [hy'.2]⟩)

theorem poleFreeKernel_rectangle (n : ℕ) (b : ℂ) {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) (T : ℝ) :
    (∫ t in -T..T, poleFreeKernel n b ((t : ℂ) + u * I) -
      poleFreeKernel n b ((t : ℂ) + v * I)) +
      I * (∫ y in u..v, poleFreeKernel n b ((T : ℂ) + y * I)) -
      I * (∫ y in u..v, poleFreeKernel n b ((-T : ℝ) + y * I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (poleFreeKernel n b) ((-T : ℝ) + u * I) ((T : ℂ) + v * I) (by
      intro w hw
      have hy := hw.2
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
        add_zero, zero_add] at hy
      have hu' := abs_lt.mp hu
      have hv' := abs_lt.mp hv
      have hmin : -1 < min u v := lt_min hu'.1 hv'.1
      have hmax : max u v < 1 := max_lt hu'.2 hv'.2
      exact (poleFreeKernel_analytic n b
        (abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)).differentiableAt.differentiableWithinAt)
  rw [intervalIntegral.integral_sub
    ((poleFreeKernel_horizontal_continuous n b hu).intervalIntegrable _ _)
    ((poleFreeKernel_horizontal_continuous n b hv).intervalIntegrable _ _)]
  simpa [smul_eq_mul] using h

theorem poleFreeKernel_horizontal_eq (n : ℕ) (b : ℂ) {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    (∫ t : ℝ, poleFreeKernel n b ((t : ℂ) + u * I)) =
      ∫ t : ℝ, poleFreeKernel n b ((t : ℂ) + v * I) := by
  have hh := intervalIntegral_tendsto_integral
    ((poleFreeKernel_horizontal_integrable n b hu).sub
      (poleFreeKernel_horizontal_integrable n b hv))
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  simp only [Pi.sub_apply, id_eq] at hh
  have hr := poleFreeKernel_vertical_tendsto n b hu hv tendsto_abs_atTop_atTop
  have hl := poleFreeKernel_vertical_tendsto (T := fun T : ℝ => -T) n b hu hv
    (by simpa only [abs_neg] using tendsto_abs_atTop_atTop)
  have hlimit := (hh.add (hr.const_mul I)).sub (hl.const_mul I)
  have he : (∫ t : ℝ, poleFreeKernel n b ((t : ℂ) + u * I) -
      poleFreeKernel n b ((t : ℂ) + v * I)) = 0 := by
    apply tendsto_nhds_unique (by simpa only [mul_zero, add_zero, sub_zero] using hlimit)
    have hfun : (fun T : ℝ =>
      (∫ t in -T..T, poleFreeKernel n b ((t : ℂ) + u * I) -
        poleFreeKernel n b ((t : ℂ) + v * I)) +
        I * (∫ y in u..v, poleFreeKernel n b ((T : ℂ) + y * I)) -
        I * (∫ y in u..v, poleFreeKernel n b ((-T : ℝ) + y * I))) =
        fun _ => 0 := funext (poleFreeKernel_rectangle n b hu hv)
    rw [hfun]
    exact tendsto_const_nhds
  rw [integral_sub (poleFreeKernel_horizontal_integrable n b hu)
    (poleFreeKernel_horizontal_integrable n b hv)] at he
  exact sub_eq_zero.mp he

theorem poleFreePoint_line (c t : ℝ) :
    poleFreePoint ((4 * t + 1 - 2 * c : ℝ) + (1 - 2 * c : ℝ) * I) =
      (c : ℂ) + (-1 + I) * t := by
  unfold poleFreePoint poleFreeRotor
  push_cast
  ring_nf
  simp only [I_sq]
  ring

theorem poleFreeKernel_line (n : ℕ) (b : ℂ) (c t : ℝ) :
    poleFreeKernel n b ((4 * t + 1 - 2 * c : ℝ) + (1 - 2 * c : ℝ) * I) * 4 =
      (((c : ℂ) + (-1 + I) * t) - b) ^ n *
        (exp (Real.pi * I * (((c : ℂ) + (-1 + I) * t) ^ 2 -
          2 * (((c : ℂ) + (-1 + I) * t) - b) ^ 2 + 1 / 8)) /
          (exp (2 * Real.pi * I * ((c : ℂ) + (-1 + I) * t)) - 1) * (-1 + I)) := by
  unfold poleFreeKernel
  rw [poleFreePoint_line]
  unfold poleFreeRotor
  ring

theorem poleFreeKernel_half (n : ℕ) (b : ℂ) (t : ℝ) :
    poleFreeKernel n b (t : ℂ) =
      (siegelLine (t / 4) - b) ^ n * correctionKernel (2 * b - 1) (t / 4) / 4 := by
  have hx : poleFreePoint (t : ℂ) = siegelLine (t / 4) := by
    unfold poleFreePoint poleFreeRotor siegelLine
    push_cast
    ring
  have hc : ((2 * b - 1) + 1) / 2 = b := by ring
  simp only [poleFreeKernel, hx, correctionKernel, hc, poleFreeRotor]
  ring

theorem poleFreeKernel_integral_moment (n : ℕ) (b : ℂ) {y : ℝ} (hy : |y| < 1) :
    (∫ t : ℝ, poleFreeKernel n b ((t : ℂ) + y * I)) = correctionMoment n (2 * b - 1) := by
  rw [poleFreeKernel_horizontal_eq n b hy (by norm_num : |(0 : ℝ)| < 1)]
  simp only [ofReal_zero, zero_mul, add_zero, poleFreeKernel_half]
  rw [integral_div, Measure.integral_comp_div
    (fun t : ℝ => (siegelLine t - b) ^ n * correctionKernel (2 * b - 1) t) 4]
  norm_num [smul_eq_mul, correctionMoment,
    show (2 * b - 1 + 1) / 2 = b by ring]

end LiuWang.Proof.Campaign20260915.ZetaMordell
