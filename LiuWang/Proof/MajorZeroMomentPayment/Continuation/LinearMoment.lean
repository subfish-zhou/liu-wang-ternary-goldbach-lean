import LiuWang.Proof.MajorZeroMomentPayment.Consumer

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation

def linearShape (rho : ℂ) : ℂ :=
  (0.998 : ℂ)^(rho + 1) / (rho * (rho + 1)) -
    0.998 * (0.001 : ℂ)^rho / rho +
    (0.001 : ℂ)^(rho + 1) / (rho + 1)

theorem weighted_slice_integral {rho : ℂ} (hr : 0 < rho.re) :
    (∫ x in (0.001 : ℝ)..0.998, (0.998 - (x : ℂ)) * (x : ℂ)^(rho - 1)) =
      linearShape rho := by
  have h0 : rho ≠ 0 := by intro h; simp [h] at hr
  have h1 : rho + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hc (z : ℂ) : IntervalIntegrable (fun x : ℝ => (x : ℂ)^z) volume 0.001 0.998 := by
    have hcont : ContinuousOn (fun x : ℝ => (x : ℂ)^z) (Icc 0.001 0.998) := by
      intro x hx
      exact (Complex.continuousAt_ofReal_cpow_const x z
        (Or.inr (by linarith [hx.1]))).continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hi := hc (rho - 1)
  have hj := hc rho
  have he :
      (∫ x in (0.001 : ℝ)..0.998, (0.998 - (x : ℂ)) * (x : ℂ)^(rho - 1)) =
      ∫ x in (0.001 : ℝ)..0.998,
        0.998 * (x : ℂ)^(rho - 1) - (x : ℂ)^rho := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0.001 : ℝ) ≤ 0.998)] at hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hx.1])
    have hp := Complex.cpow_add (rho - 1) 1 hx0
    simp only [sub_add_cancel, Complex.cpow_one] at hp
    dsimp only
    rw [hp]
    ring
  rw [he, intervalIntegral.integral_sub (hi.const_mul _) hj,
    intervalIntegral.integral_const_mul, integral_cpow (Or.inl (by simpa using hr)),
    integral_cpow (Or.inl (by linarith : -1 < rho.re))]
  simp only [sub_add_cancel]
  have hb := Complex.cpow_add rho 1 (by norm_num : (0.998 : ℂ) ≠ 0)
  simp only [Complex.cpow_one] at hb
  unfold linearShape
  push_cast
  rw [hb]
  field_simp [h0, h1]
  ring

theorem fullMoment_linear {N : ℕ} (hN : 0 < N) {rho : ℂ} (hr : 0 < rho.re) :
    fullMoment N rho 1 1 = (N : ℂ)^2 * (N : ℂ)^(rho - 1) * linearShape rho := by
  rw [fullMoment_eq_simplex hN, sourceSimplex_eq_triangle,
    integral_triangle_eq_iterated _ (simplex_cpow_integrableOn
      (N : ℝ) (Nat.cast_pos.mpr hN) rho 1 1)]
  simp only [sub_self, Complex.cpow_zero, mul_one, intervalIntegral.integral_const,
    Complex.real_smul]
  have he :
      (∫ x in (0.001 : ℝ)..0.998,
        (((0.999 - x) - 0.001 : ℝ) : ℂ) * (((N : ℝ) * x : ℝ) : ℂ)^(rho - 1)) =
      (N : ℂ)^(rho - 1) *
        ∫ x in (0.001 : ℝ)..0.998, (0.998 - (x : ℂ)) * (x : ℂ)^(rho - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0.001 : ℝ) ≤ 0.998)] at hx
    dsimp only
    rw [Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg N) (by linarith [hx.1])]
    push_cast
    ring
  rw [he, weighted_slice_integral hr]
  ring

theorem finiteMoment_linear_permute (N : ℕ) (delta : ℝ) (rho : ℂ) :
    finiteMoment N delta 1 1 rho = finiteMoment N delta rho 1 1 := by
  unfold finiteMoment
  congr 1
  ext eta
  unfold tripleKernel
  ring

def linearShapeBound (rho : ℂ) : ℝ :=
  (0.998 : ℝ)^(rho.re + 1) / (‖rho‖ * ‖rho + 1‖) +
    0.998 * (0.001 : ℝ)^rho.re / ‖rho‖ +
    (0.001 : ℝ)^(rho.re + 1) / ‖rho + 1‖

theorem norm_linearShape_le (rho : ℂ) : ‖linearShape rho‖ ≤ linearShapeBound rho := by
  have ha (z : ℂ) : ‖(0.001 : ℂ)^z‖ = (0.001 : ℝ)^z.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 0.001) z
  have hb (z : ℂ) : ‖(0.998 : ℂ)^z‖ = (0.998 : ℝ)^z.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 0.998) z
  unfold linearShape linearShapeBound
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans_eq
  simp only [norm_div, norm_mul]
  rw [hb, ha, ha]
  norm_num

theorem norm_fullMoment_linear {N : ℕ} (hN : 0 < N) {rho : ℂ} (hr : 0 < rho.re) :
    ‖fullMoment N rho 1 1‖ ≤ (N : ℝ)^2 * baseWeight N rho.re * linearShapeBound rho := by
  have hn : ‖(N : ℂ)^(rho - 1)‖ = (N : ℝ)^(rho.re - 1) := by
    simpa only [Complex.ofReal_natCast, Complex.sub_re, Complex.one_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hN) (rho - 1)
  rw [fullMoment_linear hN hr, norm_mul, norm_mul, norm_pow,
    Complex.norm_natCast, hn]
  exact mul_le_mul_of_nonneg_left (norm_linearShape_le rho) (by positivity)

end LiuWang.Proof.MajorZeroMomentPayment.Continuation
