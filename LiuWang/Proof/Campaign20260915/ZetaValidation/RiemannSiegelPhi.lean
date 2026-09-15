import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option autoImplicit false
noncomputable section
open Real

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rs_sinc_analytic (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  rw [Real.sinc_eq_dslope]
  by_cases hx : x = 0
  · subst x
    obtain ⟨p, hp⟩ := (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0)
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have he : dslope Real.sin 0 =ᶠ[nhds x] fun y => Real.sin y / y := by
      filter_upwards [dslope_eventuallyEq_slope_of_ne Real.sin hx] with y hy
      simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm] using hy
    exact (Real.analyticAt_sin.div analyticAt_id hx).congr he.symm

theorem rs_sinc_mul (x : ℝ) : x * Real.sinc x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

theorem rs_sinc_pos {x : ℝ} (hx : |x| < Real.pi) : 0 < Real.sinc x := by
  have hpos (y : ℝ) (hy : 0 < y) (hp : y < Real.pi) : 0 < Real.sinc y := by
    rw [Real.sinc_of_ne_zero hy.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hy hp) hy
  rcases lt_trichotomy x 0 with hn | rfl | hp
  · rw [← Real.sinc_neg]
    exact hpos (-x) (neg_pos.mpr hn) (by rwa [abs_of_neg hn] at hx)
  · simp
  · exact hpos x hp (by rwa [abs_of_pos hp] at hx)

def rsPhi (z : ℝ) : ℝ :=
  Real.sinc (Real.pi / 2 * (z ^ 2 - 1 / 4)) /
    (Real.pi * (Real.sinc (Real.pi / 2 * (z + 1 / 2)) *
      Real.sinc (Real.pi / 2 * (z - 1 / 2))))

theorem rsPhi_denominator_pos {z : ℝ} (hz : |z| < 3 / 2) :
    0 < Real.pi * (Real.sinc (Real.pi / 2 * (z + 1 / 2)) *
      Real.sinc (Real.pi / 2 * (z - 1 / 2))) := by
  have hp : |Real.pi / 2 * (z + 1 / 2)| < Real.pi := by
    rw [abs_lt]
    have h := abs_lt.mp hz
    constructor <;> nlinarith [h.1, h.2, Real.pi_pos]
  have hm : |Real.pi / 2 * (z - 1 / 2)| < Real.pi := by
    rw [abs_lt]
    have h := abs_lt.mp hz
    constructor <;> nlinarith [h.1, h.2, Real.pi_pos]
  exact mul_pos Real.pi_pos (mul_pos (rs_sinc_pos hp) (rs_sinc_pos hm))

theorem rsPhi_analytic {z : ℝ} (hz : |z| < 3 / 2) : AnalyticAt ℝ rsPhi z := by
  have hn : AnalyticAt ℝ (fun x : ℝ => Real.sinc (Real.pi / 2 * (x ^ 2 - 1 / 4))) z :=
    (rs_sinc_analytic _).comp (by fun_prop)
  have hp : AnalyticAt ℝ (fun x : ℝ => Real.sinc (Real.pi / 2 * (x + 1 / 2))) z :=
    (rs_sinc_analytic _).comp (by fun_prop)
  have hm : AnalyticAt ℝ (fun x : ℝ => Real.sinc (Real.pi / 2 * (x - 1 / 2))) z :=
    (rs_sinc_analytic _).comp (by fun_prop)
  exact hn.div (analyticAt_const.mul (hp.mul hm)) (rsPhi_denominator_pos hz).ne'

theorem rsPhi_even (z : ℝ) : rsPhi (-z) = rsPhi z := by
  unfold rsPhi
  rw [neg_sq, show Real.pi / 2 * (-z + 1 / 2) = -(Real.pi / 2 * (z - 1 / 2)) by ring,
    show Real.pi / 2 * (-z - 1 / 2) = -(Real.pi / 2 * (z + 1 / 2)) by ring,
    Real.sinc_neg, Real.sinc_neg, mul_comm (Real.sinc (Real.pi / 2 * (z - 1 / 2)))]

theorem rsPhi_half : rsPhi (1 / 2) = 1 / 2 := by
  norm_num [rsPhi, Real.sinc_of_ne_zero (half_pos Real.pi_pos).ne', Real.pi_ne_zero]
  field_simp

theorem rsPhi_neg_half : rsPhi (-(1 / 2)) = 1 / 2 := by
  rw [rsPhi_even, rsPhi_half]

theorem rsPhi_cos_identity {z : ℝ} (hz : |z| < 3 / 2) :
    rsPhi z * Real.cos (Real.pi * z) = Real.cos (Real.pi * (4 * z ^ 2 + 3) / 8) := by
  have hd := rsPhi_denominator_pos hz
  have hc : Real.cos (Real.pi * z) =
      -2 * Real.sin (Real.pi / 2 * (z + 1 / 2)) *
        Real.sin (Real.pi / 2 * (z - 1 / 2)) := by
    have h := Real.cos_sub_cos (Real.pi * z) (Real.pi / 2)
    rw [Real.cos_pi_div_two, sub_zero] at h
    convert h using 1
    congr 2 <;> ring
  have hn : Real.cos (Real.pi * (4 * z ^ 2 + 3) / 8) =
      -Real.sin (Real.pi / 2 * (z ^ 2 - 1 / 4)) := by
    rw [show Real.pi * (4 * z ^ 2 + 3) / 8 =
      Real.pi / 2 + Real.pi / 2 * (z ^ 2 - 1 / 4) by ring, Real.cos_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [hc, hn, ← rs_sinc_mul (Real.pi / 2 * (z + 1 / 2)),
    ← rs_sinc_mul (Real.pi / 2 * (z - 1 / 2)),
    ← rs_sinc_mul (Real.pi / 2 * (z ^ 2 - 1 / 4))]
  unfold rsPhi
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hd.ne').mpr
  ring

theorem rsPhi_eq_printed {z : ℝ} (hz : |z| < 3 / 2) (hc : Real.cos (Real.pi * z) ≠ 0) :
    rsPhi z = Real.cos (Real.pi * (4 * z ^ 2 + 3) / 8) / Real.cos (Real.pi * z) :=
  (eq_div_iff hc).mpr (rsPhi_cos_identity hz)

theorem rsPhi_iterated_deriv_analytic {z : ℝ} (hz : |z| < 3 / 2) (n : ℕ) :
    AnalyticAt ℝ (deriv^[n] rsPhi) z :=
  (rsPhi_analytic hz).iterated_deriv n

end LiuWang.Proof.Campaign20260915.ZetaValidation
