import LiuWang.Proof.MajorZeroMomentPayment.Continuation.R24Gap

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier

theorem Jrho_primitive_parts {N : ℕ} (hN : 0 < N) (rho : ℂ) (eta : ℝ) :
    rho * Jrho N rho eta =
      (N : ℂ)^rho * charReal (eta * N) -
      (sourceWindowLower N : ℂ)^rho * charReal (eta * sourceWindowLower N) -
      (2 * Real.pi * eta * Complex.I) *
        ∫ t in sourceWindowLower N..(N : ℝ), (t : ℂ)^rho * charReal (eta*t) := by
  have hd : ∀ t ∈ uIcc (sourceWindowLower N) (N : ℝ),
      HasDerivAt (fun t : ℝ => (t : ℂ)^rho) (rho*(t : ℂ)^(rho-1)) t := by
    intro t ht
    rw [uIcc_of_le (window_lower_le N)] at ht
    exact cpow_hasDerivAt ((window_lower_pos hN).trans_le ht.1) rho
  have hi := (cpow_intervalIntegrable hN (rho-1)).const_mul rho
  have he := (OscillatoryBounds.intervalIntegrable_charReal
    (sourceWindowLower N) N eta).mul_const (2*Real.pi*eta*Complex.I)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => OscillatoryBounds.hasDerivAt_charReal_mul eta t) hd he hi
  convert h using 1
  · rw [Jrho, ← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  · rw [← intervalIntegral.integral_const_mul]
    simp only [Complex.ofReal_natCast]
    have heq : (∫ t in sourceWindowLower N..(N : ℝ),
        (2 * Real.pi * eta * Complex.I) * ((t : ℂ)^rho * charReal (eta*t))) =
        ∫ t in sourceWindowLower N..(N : ℝ),
          (charReal (eta*t) * (2*Real.pi*eta*Complex.I)) * (t : ℂ)^rho := by
      congr 1
      ext t
      ring
    rw [heq]
    ring

theorem Jrho_norm_mul_rho {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hb : 0 ≤ rho.re) (eta : ℝ) :
    ‖rho‖ * ‖Jrho N rho eta‖ ≤
      2 * (N : ℝ)^rho.re * (1 + Real.pi * (N : ℝ) * |eta|) := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hp (t : ℝ) (ht : t ∈ Icc (sourceWindowLower N) (N : ℝ)) :
      ‖(t : ℂ)^rho * charReal (eta*t)‖ ≤ (N : ℝ)^rho.re := by
    rw [norm_mul, charReal_norm, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos ((window_lower_pos hN).trans_le ht.1)]
    exact Real.rpow_le_rpow ((window_lower_pos hN).trans_le ht.1).le ht.2 hb
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := sourceWindowLower N) (b := (N : ℝ)) (C := (N : ℝ)^rho.re)
    (f := fun t => (t : ℂ)^rho * charReal (eta*t)) (fun t ht => by
      rw [uIoc_of_le (window_lower_le N)] at ht
      exact hp t ⟨ht.1.le, ht.2⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr (window_lower_le N))] at hint
  have hint' : ‖∫ t in sourceWindowLower N..(N : ℝ), (t : ℂ)^rho * charReal (eta*t)‖ ≤
      (N : ℝ)^rho.re * (N : ℝ) :=
    hint.trans (mul_le_mul_of_nonneg_left (by linarith [window_lower_pos hN]) (by positivity))
  have h := norm_sub_le
    ((N : ℂ)^rho * charReal (eta*N) -
      (sourceWindowLower N : ℂ)^rho * charReal (eta*sourceWindowLower N))
    ((2 * Real.pi * eta * Complex.I) *
      ∫ t in sourceWindowLower N..(N : ℝ), (t : ℂ)^rho * charReal (eta*t))
  have hh := norm_sub_le ((N : ℂ)^rho * charReal (eta*N))
    ((sourceWindowLower N : ℂ)^rho * charReal (eta*sourceWindowLower N))
  rw [← Jrho_primitive_parts hN, norm_mul, norm_mul, OscillatoryBounds.norm_frequency] at h
  have he := mul_le_mul_of_nonneg_left hint' (by positivity : 0 ≤ 2*Real.pi*|eta|)
  have htop := hp N ⟨window_lower_le N, le_rfl⟩
  simp only [Complex.ofReal_natCast] at htop
  have hbot := hp (sourceWindowLower N) ⟨le_rfl, window_lower_le N⟩
  nlinarith

theorem J_smooth_decay {N : ℕ} (hN : 0 < N) (eta : ℝ) :
    ‖J N eta‖ * (1 + Real.pi * (N : ℝ) * |eta|) ≤ 2 * (N : ℝ) := by
  have h := J_abs_mul_norm_le hN eta
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ Real.pi * (N : ℝ))
  have he : Real.pi * (N : ℝ) * (1 / Real.pi) = (N : ℝ) := by field_simp
  rw [he] at hh
  nlinarith [J_norm_le_length N eta, Nat.cast_nonneg (α := ℝ) N]

theorem linear_kernel_direct {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hb : 0 ≤ rho.re) (hr : rho ≠ 0) (eta : ℝ) :
    ‖tripleKernel N 1 1 rho eta‖ ≤
      8 * (N : ℝ)^2 * (N : ℝ)^rho.re /
        (‖rho‖ * (1 + Real.pi * (N : ℝ) * |eta|)) := by
  let d := 1 + Real.pi * (N : ℝ) * |eta|
  have hd : 0 < d := by dsimp [d]; positivity
  have hj : ‖J N eta‖ ≤ 2 * (N : ℝ) / d :=
    (le_div_iff₀ hd).mpr (J_smooth_decay hN eta)
  have hz : ‖Jrho N rho eta‖ ≤ 2 * (N : ℝ)^rho.re * d / ‖rho‖ := by
    apply (le_div_iff₀ (norm_pos_iff.mpr hr)).mpr
    simpa only [d, mul_comm] using Jrho_norm_mul_rho hN hb eta
  simp only [tripleKernel, norm_mul, charReal_norm, one_mul, Jrho_one_eq_J]
  calc
    _ ≤ (2*(N : ℝ)/d) * (2*(N : ℝ)/d) * (2*(N : ℝ)^rho.re*d/‖rho‖) :=
      mul_le_mul (mul_le_mul hj hj (norm_nonneg _) (by positivity)) hz
        (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [d] at *; field_simp; ring

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier
