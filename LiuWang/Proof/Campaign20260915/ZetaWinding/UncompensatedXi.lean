import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanXiSeries
import LiuWang.Proof.ZeroRegionFamily.Sharp.ZetaKernel

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.ChebyshevBound.HighHeight

theorem xi_uncompensated_logDeriv_summable {s : ℂ}
    (hs : ∀ p : RiemannXiDivisorZeroIndex, s ≠ riemannXiDivisorZeroValue p) :
    Summable (fun p : RiemannXiDivisorZeroIndex => (1 / (s - riemannXiDivisorZeroValue p)).re) := by
  have h := (Complex.reCLM.summable
    (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hs)).sub xi_inv_re_summable
  change Summable (fun p : RiemannXiDivisorZeroIndex =>
    (1 / (s - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p).re -
      (1 / riemannXiDivisorZeroValue p).re) at h
  simpa only [add_re, add_sub_cancel_right] using h

theorem xi_uncompensated_logDeriv {s : ℂ}
    (hs : ∀ p : RiemannXiDivisorZeroIndex, s ≠ riemannXiDivisorZeroValue p) :
    (logDeriv riemannXi s).re =
      ∑' p : RiemannXiDivisorZeroIndex, (1 / (s - riemannXiDivisorZeroValue p)).re := by
  rw [xi_hadamard_logDeriv hs, add_re]
  simp only [xiTerm]
  rw [Complex.re_tsum (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hs)]
  simp only [add_re]
  rw [(xi_uncompensated_logDeriv_summable hs).tsum_add xi_inv_re_summable, xi_inv_re_sum]
  ring

theorem xi_uncompensated_integral_summable {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ∫ x in a..b, Real.log ‖(horizontalAt T x - riemannXiDivisorZeroValue p) /
        (horizontalAt T (x + 1) - riemannXiDivisorZeroValue p)‖) := by
  have h := (xi_zero_ratio_integral_summable hab T).add
    (xi_inv_re_summable.mul_left (b - a))
  simpa only [one_div, sub_add_cancel] using h

theorem xi_uncompensated_horizontal_difference {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    (∫ x in a..b, Real.log ‖riemannXi (horizontalAt T x)‖) -
      (∫ x in (a + 1)..(b + 1), Real.log ‖riemannXi (horizontalAt T x)‖) =
      ∑' p : RiemannXiDivisorZeroIndex,
        ∫ x in a..b, Real.log ‖(horizontalAt T x - riemannXiDivisorZeroValue p) /
          (horizontalAt T (x + 1) - riemannXiDivisorZeroValue p)‖ := by
  rw [xi_horizontal_unit_shift_integral hab T]
  simp_rw [xiGenusLog_shift_eq_zero_ratio]
  have hsum := (xi_uncompensated_integral_summable hab T).tsum_sub
    (xi_inv_re_summable.mul_left (b - a))
  simp only [one_div] at hsum
  rw [hsum, tsum_mul_left]
  have hc := xi_inv_re_sum
  simp only [one_div] at hc
  rw [hc]
  ring

theorem xi_lehman_uncompensated_series (T : ℝ) :
    (∫ x in (1 / 2 : ℝ)..(3 / 2),
      Real.log ‖riemannXi (horizontalAt T x) /
        riemannXi (horizontalAt T (x + 1))‖) =
      ∑' p : RiemannXiDivisorZeroIndex,
        ∫ x in (1 / 2 : ℝ)..(3 / 2),
          Real.log ‖(horizontalAt T x - riemannXiDivisorZeroValue p) /
            (horizontalAt T (x + 1) - riemannXiDivisorZeroValue p)‖ := by
  rw [xi_lehman_unit_shift_series]
  have hsum := (xi_uncompensated_integral_summable (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) T).tsum_sub
    xi_inv_re_summable
  simp only [one_div] at hsum ⊢
  rw [hsum]
  have hc := xi_inv_re_sum
  simp only [one_div] at hc
  rw [hc]
  ring

#print axioms xi_uncompensated_logDeriv
#print axioms xi_uncompensated_integral_summable
#print axioms xi_uncompensated_horizontal_difference
#print axioms xi_lehman_uncompensated_series
#print axioms LiuWang.Proof.ZeroRegionFamily.Sharp.xi_inv_re_sum

end LiuWang.Proof.Campaign20260915.ZetaWinding
