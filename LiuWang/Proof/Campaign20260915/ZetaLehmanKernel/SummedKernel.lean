import LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.ZeroPair
import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanXiSeries

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaLehmanKernel

open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.ChebyshevBound.HighHeight

set_option maxHeartbeats 800000 in
theorem xi_zero_series_lehman (T : ℝ) :
    -(37 / 25 : ℝ) * (logDeriv riemannXi (horizontalAt T (3 / 2))).re ≤
      ∑' p : RiemannXiDivisorZeroIndex,
        ∫ x in (1 / 2 : ℝ)..(3 / 2),
          Real.log ‖(horizontalAt T x - riemannXiDivisorZeroValue p) /
            (horizontalAt T (x + 1) - riemannXiDivisorZeroValue p)‖ := by
  let f := fun p : RiemannXiDivisorZeroIndex => zeroIntegral (riemannXiDivisorZeroValue p) T
  let g := fun p : RiemannXiDivisorZeroIndex => referenceTerm (riemannXiDivisorZeroValue p) T
  have hc := xi_zero_ratio_integral_summable (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) T
  norm_num only [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, one_mul] at hc
  have hf : Summable f := by
    simpa only [f, zeroIntegral, one_div, sub_add_cancel] using hc.add xi_inv_re_summable
  have href : 1 ≤ (horizontalAt T (3 / 2)).re := by norm_num [horizontalAt]
  have hg : Summable g := xi_raw_summable href
  have hfr : Summable (fun p => f (xiReflection p)) := xiReflection.summable_iff.mpr hf
  have hgr : Summable (fun p => g (xiReflection p)) := xiReflection.summable_iff.mpr hg
  have hp (p : RiemannXiDivisorZeroIndex) :
      -(37 / 25 : ℝ) * (g p + g (xiReflection p)) ≤ f p + f (xiReflection p) :=
    xi_zero_pair_lehman T p
  have hs := ((hg.add hgr).mul_left (-(37 / 25 : ℝ))).tsum_le_tsum hp (hf.add hfr)
  rw [tsum_mul_left, hg.tsum_add hgr, hf.tsum_add hfr,
    xiReflection.tsum_eq g, xiReflection.tsum_eq f] at hs
  have hd := congrArg Complex.re (xi_hadamard_logDeriv (xi_reference_ne_zero T))
  rw [add_re, Complex.re_tsum (xiTerm_summable href)] at hd
  have he (p : RiemannXiDivisorZeroIndex) :
      (xiTerm (horizontalAt T (3 / 2)) p).re =
        g p + (1 / riemannXiDivisorZeroValue p).re := by
    simp [g, referenceTerm, xiTerm]
  simp_rw [he] at hd
  rw [hg.tsum_add xi_inv_re_summable, xi_inv_re_sum] at hd
  change -(37 / 25 : ℝ) * (logDeriv riemannXi (horizontalAt T (3 / 2))).re ≤ ∑' p, f p
  linarith

theorem xi_lehman_log_integral_lower (T : ℝ) :
    -(37 / 25 : ℝ) * (logDeriv riemannXi (horizontalAt T (3 / 2))).re ≤
      ∫ x in (1 / 2 : ℝ)..(3 / 2),
        Real.log ‖riemannXi (horizontalAt T x) /
          riemannXi (horizontalAt T (x + 1))‖ := by
  have hc := xi_zero_ratio_integral_summable (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) T
  norm_num only [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, one_mul] at hc
  have he := hc.tsum_add xi_inv_re_summable
  simp only [one_div, sub_add_cancel] at he
  have hi := xi_inv_re_sum
  simp only [one_div] at hi
  rw [hi] at he
  rw [xi_lehman_unit_shift_series]
  have hs := xi_zero_series_lehman T
  linarith

#print axioms xi_zero_series_lehman
#print axioms xi_lehman_log_integral_lower

end LiuWang.Proof.Campaign20260915.ZetaLehmanKernel
