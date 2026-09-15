import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelKernel

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsSaddleScale : ℝ := Real.sqrt (2 * Real.pi)

def rsDescentDirection : ℂ := (1 - I) / Real.sqrt 2

def rsDescentPoint (eta y : ℝ) : ℂ := eta + rsDescentDirection * y

def rsGaussianKernel (eta : ℝ) (m : ℕ) (x : ℂ) : ℂ :=
  exp (-Real.pi * I * (x - eta) ^ 2 +
    2 * Real.pi * I * (eta - (m : ℝ)) * (x - eta)) / rsHankelDenominator x

theorem rsSaddleScale_pos : 0 < rsSaddleScale := by
  exact Real.sqrt_pos.mpr (by positivity)

theorem rsSaddleScale_sq : rsSaddleScale ^ 2 = 2 * Real.pi :=
  Real.sq_sqrt (by positivity)

theorem rsDescentDirection_norm : ‖rsDescentDirection‖ = 1 := by
  unfold rsDescentDirection
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]
  have hn : ‖(1 - I : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_def]
    norm_num [normSq_apply]
  rw [hn, div_self (Real.sqrt_ne_zero'.mpr (by norm_num))]

theorem rsDescentPoint_distance (eta y : ℝ) :
    ‖rsDescentPoint eta y - eta‖ = |y| := by
  rw [rsDescentPoint, add_sub_cancel_left, norm_mul, rsDescentDirection_norm,
    norm_real, Real.norm_eq_abs, one_mul]

theorem rsHankelLog_eq_principal {x : ℂ} (hx : 0 < x.re) :
    rsHankelLog x = log x := by
  have harg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hlog := (log_mul_eq_add_log_iff (neg_ne_zero.mpr I_ne_zero)
    (ne_zero_of_re_pos hx)).mpr (by
      rw [arg_neg_I]
      constructor <;> linarith [Real.pi_pos])
  rw [rsHankelLog, hlog, log_neg_I]
  ring

theorem rsHankelKernel_saddle_factor (sigma : ℝ) (m : ℕ) {eta : ℝ}
    (he : 0 < eta) {x : ℂ} (hx : ‖x - eta‖ < eta) :
    rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) m x =
      (eta : ℂ) ^ (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) - 1) *
        exp (-2 * Real.pi * I * m * eta) * rsGaussianKernel eta m x *
          rsSaddleWeight sigma (rsSaddleScale * eta) (rsSaddleScale * (x - eta)) := by
  have hxR : 0 < x.re := by
    have h := (abs_le.mp (abs_re_le_norm (x - eta))).1
    simp only [sub_re, ofReal_re] at h
    linarith
  have hn : 1 + (x - eta) / (eta : ℂ) ≠ 0 :=
    slitPlane_ne_zero (rsSaddle_slit he hx)
  have hlog : log x = (Real.log eta : ℂ) + log (1 + (x - eta) / eta) := by
    rw [← log_ofReal_mul he hn]
    congr 1
    field_simp [ofReal_ne_zero.mpr he.ne']
    ring
  have hs : (rsSaddleScale : ℂ) ^ 2 = 2 * Real.pi := by
    exact_mod_cast rsSaddleScale_sq
  have hc : (rsSaddleScale : ℂ) ≠ 0 := ofReal_ne_zero.mpr rsSaddleScale_pos.ne'
  have heC : (eta : ℂ) ≠ 0 := ofReal_ne_zero.mpr he.ne'
  have hquot : (rsSaddleScale : ℂ) * (x - eta) / ((rsSaddleScale * eta : ℝ) : ℂ) =
      (x - eta) / eta := by push_cast; field_simp
  unfold rsHankelKernel rsHankelNumerator rsGaussianKernel rsSaddleWeight rsSaddleExponent
  rw [rsHankelLog_eq_principal hxR, hlog, cpow_def_of_ne_zero heC,
    ← ofReal_log he.le, hquot]
  push_cast
  have heq :
      (((sigma : ℂ) + I * ((rsSaddleScale : ℂ) * eta) ^ 2) - 1) *
          ((Real.log eta : ℂ) + log (1 + (x - eta) / eta)) - 2 * Real.pi * I * m * x =
      log (eta : ℂ) * (((sigma : ℂ) + I * ((rsSaddleScale : ℂ) * eta) ^ 2) - 1) +
        (-2 * Real.pi * I * m * eta) +
        (-Real.pi * I * (x - eta) ^ 2 +
          2 * Real.pi * I * (eta - (m : ℂ)) * (x - eta)) +
        (((sigma : ℂ) - 1 + I * ((rsSaddleScale : ℂ) * eta) ^ 2) *
          log (1 + (x - eta) / eta) -
          I * ((rsSaddleScale : ℂ) * eta) * ((rsSaddleScale : ℂ) * (x - eta)) +
          I / 2 * ((rsSaddleScale : ℂ) * (x - eta)) ^ 2) := by
    rw [← ofReal_log he.le]
    ring_nf
    rw [hs]
    ring
  rw [heq, exp_add, exp_add, exp_add]
  rw [← ofReal_log he.le]
  ring

end LiuWang.Proof.Campaign20260915.ZetaValidation
