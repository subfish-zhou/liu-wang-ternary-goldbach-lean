import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.ZeroTransport

/-! LWD (2.5)--(2.6); the two McCurley Gamma estimates remain explicit inputs. -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

def principalEulerDifference (q : ℕ) (sigma t : ℝ) : ℝ :=
  (logDeriv (principalLevelCorrection q) ((sigma : ℂ) + I * t) -
    (stechkinK : ℂ) *
      logDeriv (principalLevelCorrection q) ((stechkinSigma sigma : ℂ) + I * t)).re

theorem l24_euler_identity {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) :
    f (1 : DirichletCharacter ℂ q) sigma t =
      zetaDamped sigma t - principalEulerDifference q sigma t := by
  rw [f_eq_damped]
  unfold dampedLogDeriv
  rw [logDeriv_principal_eq_levelCorrection_add_riemannZeta
      (by simpa [mul_re] using hs),
    logDeriv_principal_eq_levelCorrection_add_riemannZeta
      (by simpa [mul_re] using hs.trans_le (stechkinSigma_ge hs))]
  simp only [principalEulerDifference, zetaDamped, add_re, sub_re, mul_re,
    ofReal_re, ofReal_im, zero_mul, sub_zero]
  ring

theorem principalEulerDifference_bound (q : ℕ) {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) :
    |principalEulerDifference q sigma t| ≤ s q sigma := by
  rw [s_eq]
  exact (abs_re_le_norm _).trans (norm_principal_level_difference_le q hs t)

theorem l24_zeta_identity {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    zetaDamped sigma t = poleDifference sigma t - kappa * Real.log Real.pi +
      gammaTerm 2 sigma t - zetaZeroSum sigma t := by
  have hi := zeta_full_zero_sum_identity hs t
  have he (u : ℝ) : ((u : ℂ) + I * t) / 2 + 1 =
      ((u : ℂ) + I * t + 2) / 2 := by ring
  simp only [shiftedGammaDifference, he] at hi
  rw [kappa_eq]
  simp only [gammaTerm, ofReal_ofNat]
  linarith

theorem l24_principal_identity {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) :
    f (1 : DirichletCharacter ℂ q) sigma t =
      poleDifference sigma t - kappa * Real.log Real.pi + gammaTerm 2 sigma t -
        zetaZeroSum sigma t - principalEulerDifference q sigma t := by
  rw [l24_euler_identity hs, l24_zeta_identity hs]

theorem poleDifference_le_reciprocal {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    poleDifference sigma t ≤ (1 / ((sigma : ℂ) - 1 + I * t)).re := by
  have hpos : 0 ≤ (1 / ((stechkinSigma sigma : ℂ) - 1 + I * t)).re := by
    rw [one_div, inv_re]
    apply div_nonneg _ (normSq_nonneg _)
    simpa [mul_re] using (sub_nonneg.mpr (hs.trans_le (stechkinSigma_ge hs)).le)
  exact sub_le_self _ (mul_nonneg stechkinK_mem.1 hpos)

theorem l24_low_of_gamma_estimate {q : ℕ} [NeZero q] {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : |t| < 1)
    (hgamma : ∀ u : ℝ, |u| < 1 → gammaTerm 2 sigma u < 0.0615) :
    f (1 : DirichletCharacter ℂ q) sigma t <
      (1 / ((sigma : ℂ) - 1 + I * t)).re - kappa * Real.log Real.pi +
        0.0615 + s q sigma - zetaZeroSum sigma t := by
  rw [l24_principal_identity hs.1]
  have hg := hgamma t ht
  have hp := poleDifference_le_reciprocal hs.1 t
  have he := (neg_le_abs (principalEulerDifference q sigma t)).trans
    (principalEulerDifference_bound q hs.1 t)
  linarith

theorem l24_high_of_gamma_estimate {q : ℕ} [NeZero q] {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : 1 ≤ |t|)
    (hgamma : gammaTerm 2 sigma t < kappa * Real.log |t| + 0.3316) :
    f (1 : DirichletCharacter ℂ q) sigma t <
      kappa * Real.log |t| - kappa * Real.log Real.pi +
        0.3316 + s q sigma - zetaZeroSum sigma t := by
  rw [l24_principal_identity hs.1]
  have hp := poleDifference_high_nonpos hs.1 (by linarith [hs.2]) ht
  have he := (neg_le_abs (principalEulerDifference q sigma t)).trans
    (principalEulerDifference_bound q hs.1 t)
  linarith

end LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
