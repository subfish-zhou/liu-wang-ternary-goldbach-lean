import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases.ZetaSelection

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal

def offDebit (sigma beta t : ℝ) : ℝ :=
  realKernel (sigma - beta) t - (5 + Real.sqrt 5) / 10

def nearDebit (sigma beta t : ℝ) : ℝ :=
  if |t| < 1 then offDebit sigma beta t else 0

def principalCost (y : ℝ) : ℝ :=
  stechkinConductorCoeff * Real.log y -
    stechkinConductorCoeff * Real.log Real.pi + 0.3316

theorem nearDebit_le_reflected {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1) (t : ℝ) :
    nearDebit sigma rho.re (t - rho.im) ≤ reflectedKernel sigma t rho := by
  unfold nearDebit
  split_ifs with h
  · exact lwd_2_16_kernel hs hs1 hr.le hr1 h.le
  · exact dampedZeroKernel_pair_nonneg hs t ⟨by linarith, hr1.le⟩

theorem low_cost_absorb {y : ℝ} (hy : 8000000000 ≤ y) :
    0.0615 + 2 * ((5 + Real.sqrt 5) / 10) ≤
      stechkinConductorCoeff * Real.log y + 0.3316 := by
  have hsqrt : Real.sqrt 5 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hh := mul_le_mul_of_nonneg_left (source_log_twenty_two hy) conductorCoeff_bounds.1
  linarith [lwd_kappa_bounds.1]

theorem high_cost {sigma t y : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    (ht : 1 ≤ |t|) (hty : |t| ≤ y)
    (hgamma : gammaHalfDifference sigma t <
      stechkinConductorCoeff * Real.log |t| + 0.3316) :
    zetaDamped sigma t ≤ principalCost y := by
  have hh := zeta_high_unselected hs hs1 ht hgamma.le
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_log (by linarith : 0 < |t|) hty) conductorCoeff_bounds.1
  unfold principalCost
  linarith

theorem low_two_debits {sigma t y beta eta : ℝ} (hs : 1 < sigma)
    (hy : 8000000000 ≤ y) (hb : beta < 1) (he : eta < 1)
    (hgb : 1 - beta ≤ sigma - 1) (hge : 1 - eta ≤ sigma - 1)
    (hgamma : gammaHalfDifference sigma t < 0.0615) :
    zetaDamped sigma t - offDebit sigma beta t - offDebit sigma eta t ≤
      principalCost y := by
  have hz := lwd_2_21 hs hgamma.le
  have hp := lwd_G_lemma_two (u := t) hs hb he hgb hge
  have hk : realKernel (sigma - 1) t = (1 / ((sigma : ℂ) - 1 + I * t)).re := by
    simp only [realKernel_eq_inverse_re, Complex.ofReal_sub, Complex.ofReal_one]
  rw [← hk] at hz
  unfold offDebit principalCost
  linarith [low_cost_absorb hy]

theorem pair_cost {sigma t y beta eta : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15)
    (hy : 8000000000 ≤ y) (hty : |t| ≤ y) (hb : beta < 1) (he : eta < 1)
    (hgb : 1 - beta ≤ sigma - 1) (hge : 1 - eta ≤ sigma - 1)
    (hgammaHigh : ∀ u : ℝ, 1 ≤ |u| →
      gammaHalfDifference sigma u < stechkinConductorCoeff * Real.log |u| + 0.3316)
    (hgammaLow : ∀ u : ℝ, |u| < 1 → gammaHalfDifference sigma u < 0.0615) :
    zetaDamped sigma t - nearDebit sigma beta t - nearDebit sigma eta t ≤
      principalCost y := by
  by_cases ht : |t| < 1
  · simpa only [nearDebit, if_pos ht] using
      low_two_debits hs hy hb he hgb hge (hgammaLow t ht)
  · simpa only [nearDebit, if_neg ht, sub_zero] using
      high_cost hs hs1 (le_of_not_gt ht) hty (hgammaHigh t (le_of_not_gt ht))

theorem case_i_constant :
    -0.8973 + 7 * 0.3316 +
      stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) ≤
        0.0876 := by
  have hl : 3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi ≤
      3 * 0.693147181 + 1.098612289 - 7 * 1.144729 := by
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, lwd_log_pi]
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  have hk := mul_le_mul_of_nonpos_right lwd_kappa_bounds.1
    (by norm_num : 3 * (0.693147181 : ℝ) + 1.098612289 - 7 * 1.144729 ≤ 0)
  linarith

theorem seven_costs {x : ℝ} (hx : 0 < x) :
    -0.8973 + 3 * principalCost x + 3 * principalCost (2 * x) + principalCost (3 * x) ≤
      7 * stechkinConductorCoeff * Real.log x + 0.0876 := by
  unfold principalCost
  rw [Real.log_mul (by norm_num) hx.ne', Real.log_mul (by norm_num) hx.ne']
  nlinarith only [case_i_constant]

theorem triple_close_pair_high {t u v : ℝ} (hv : 2 ≤ |v|)
    (ht : |t + u + v| < 1) : 1 ≤ |t + u| := by
  have hh := abs_add_le (t + u + v) (-(t + u))
  rw [show t + u + v + -(t + u) = v by ring, abs_neg] at hh
  linarith

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal
