import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelSourceNormalization

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsHankelLift (s : ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  exp (s * w - 2 * Real.pi * I * m * exp w) / rsHankelDenominator (exp w)

def rsHankelArc (s : ℂ) (m : ℕ) (u : ℝ) : ℂ :=
  I * ∫ θ : ℝ in -(Real.pi / 2)..3 * Real.pi / 2,
    rsHankelLift s m (u + θ * I)

theorem rsHankelDenominator_ne_zero_of_norm {z : ℂ} (hz : z ≠ 0) (hn : ‖z‖ < 1) :
    rsHankelDenominator z ≠ 0 := by
  rw [ne_eq, rsHankelDenominator_zero_iff]
  rintro ⟨n, rfl⟩
  have hn0 : n ≠ 0 := by exact_mod_cast hz
  have hi : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
  have hiR : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hi
  rw [norm_intCast] at hn
  linarith

theorem rsHankelLift_analytic (s : ℂ) (m : ℕ) {w : ℂ} (hw : w.re < 0) :
    AnalyticAt ℂ (rsHankelLift s m) w := by
  apply AnalyticAt.div (by fun_prop)
    ((rsHankelDenominator_analytic _).comp (by fun_prop))
  exact rsHankelDenominator_ne_zero_of_norm (exp_ne_zero _)
    (by rw [norm_exp]; exact Real.exp_lt_one_iff.mpr hw)

theorem rsHankelLog_exp {w : ℂ}
    (hlo : -(Real.pi / 2) < w.im) (hhi : w.im < 3 * Real.pi / 2) :
    rsHankelLog (exp w) = w := by
  have he : -I * exp w = exp (w - Real.pi / 2 * I) := by
    rw [exp_sub, exp_pi_div_two_mul_I, div_I]
    ring
  rw [rsHankelLog, he, log_exp]
  · ring
  · simp only [sub_im, mul_im, div_ofNat, ofReal_im, I_re, mul_zero, ofReal_re,
      I_im, mul_one, zero_div]
    linarith
  · simp only [sub_im, mul_im, div_ofNat, ofReal_im, I_re, mul_zero, ofReal_re,
      I_im, mul_one, zero_div]
    linarith

theorem rsHankelLift_actual (s : ℂ) (m : ℕ) {w : ℂ}
    (hlo : -(Real.pi / 2) < w.im) (hhi : w.im < 3 * Real.pi / 2) :
    rsHankelLift s m w = exp w * rsHankelKernel s m (exp w) := by
  rw [rsHankelLift, rsHankelKernel, rsHankelNumerator, rsHankelLog_exp hlo hhi,
    ← mul_div_assoc, ← exp_add]
  congr 2
  ring

theorem rsHankelLift_bottom (s : ℂ) (m : ℕ) (u : ℝ) :
    rsHankelLift s m (u + (-(Real.pi / 2) : ℝ) * I) =
      (Real.exp u : ℂ) * rsHankelRightBank s m (Real.exp u) := by
  have he : exp ((u : ℂ) + (-(Real.pi / 2) : ℝ) * I) = -I * Real.exp u := by
    push_cast
    rw [← neg_div, exp_add, exp_neg_pi_div_two_mul_I, ← ofReal_exp]
    ring
  have hb := rsHankelRightBank_factor s m (Real.exp_pos u)
  rw [Real.log_exp] at hb
  rw [rsHankelLift, he, ← hb]
  have hh : s * ((u : ℂ) + (-(Real.pi / 2) : ℝ) * I) -
      2 * Real.pi * I * m * (-I * Real.exp u) =
      (u + (-(Real.pi / 2) : ℝ) * I) +
        ((s - 1) * ((u : ℂ) - Real.pi / 2 * I) -
          2 * Real.pi * I * m * (-I * Real.exp u)) := by push_cast; ring
  rw [hh, exp_add, he]
  ring

theorem rsHankelLift_top (s : ℂ) (m : ℕ) (u : ℝ) :
    rsHankelLift s m (u + (3 * Real.pi / 2 : ℝ) * I) =
      (Real.exp u : ℂ) * rsHankelLeftBank s m (Real.exp u) := by
  have hw : (u : ℂ) + (3 * Real.pi / 2 : ℝ) * I =
      (u + (-(Real.pi / 2) : ℝ) * I) + 2 * Real.pi * I := by push_cast; ring
  have he : exp ((u : ℂ) + (3 * Real.pi / 2 : ℝ) * I) =
      exp ((u : ℂ) + (-(Real.pi / 2) : ℝ) * I) := by
    rw [hw, exp_add, exp_two_pi_mul_I, mul_one]
  have hp : rsHankelLift s m (u + (3 * Real.pi / 2 : ℝ) * I) =
      exp (2 * Real.pi * I * s) *
        rsHankelLift s m (u + (-(Real.pi / 2) : ℝ) * I) := by
    unfold rsHankelLift
    rw [he, hw, mul_add, add_sub_right_comm, exp_add]
    rw [show s * (2 * Real.pi * I) = 2 * Real.pi * I * s by ring]
    ring
  rw [hp, rsHankelLift_bottom, rsHankelLeftBank]
  ring

theorem rsHankelArc_integrable (s : ℂ) (m : ℕ) {u : ℝ} (hu : u < 0) :
    IntervalIntegrable (fun θ : ℝ => rsHankelLift s m (u + θ * I)) volume
      (-(Real.pi / 2)) (3 * Real.pi / 2) := by
  apply ContinuousOn.intervalIntegrable
  intro θ _
  apply ContinuousAt.continuousWithinAt
  exact (rsHankelLift_analytic s m (by simpa)).continuousAt.comp (by fun_prop)

theorem rsHankelArc_difference (s : ℂ) (m : ℕ) {u v : ℝ}
    (hu : u < 0) (hv : v < 0) :
    rsHankelArc s m v - rsHankelArc s m u =
      (∫ x : ℝ in u..v, (Real.exp x : ℂ) * rsHankelLeftBank s m (Real.exp x)) -
        ∫ x : ℝ in u..v, (Real.exp x : ℂ) * rsHankelRightBank s m (Real.exp x) := by
  have hd : DifferentiableOn ℂ (rsHankelLift s m)
      ([[u, v]] ×ℂ [[-(Real.pi / 2), 3 * Real.pi / 2]]) := by
    intro w hw
    apply (rsHankelLift_analytic s m ?_).differentiableAt.differentiableWithinAt
    exact lt_of_le_of_lt hw.1.2 (max_lt hu hv)
  have h := integral_boundary_rect_eq_zero_of_differentiableOn (rsHankelLift s m)
    (u + (-(Real.pi / 2) : ℝ) * I) (v + (3 * Real.pi / 2 : ℝ) * I) (by simpa using hd)
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_self, add_zero, add_im, mul_im, mul_one, zero_add, smul_eq_mul] at h
  simp_rw [rsHankelLift_bottom, rsHankelLift_top] at h
  unfold rsHankelArc
  linear_combination h

end LiuWang.Proof.Campaign20260915.ZetaValidation
