import LiuWang.Proof.SourceRoute.MajorException.MixedMoments
import LiuWang.Proof.SourceRoute.MajorException.MixedRealMoment

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

def cubeRoot (x : ℝ) : ℝ := x^((1 : ℝ)/3)

theorem cubeRoot_pos {x : ℝ} (hx : 0 < x) : 0 < cubeRoot x :=
  Real.rpow_pos_of_pos hx _

theorem cubeRoot_cube {x : ℝ} (hx : 0 ≤ x) : cubeRoot x^3 = x := by
  rw [cubeRoot, ← Real.rpow_mul_natCast hx]
  norm_num

theorem triple_young {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3*x*y*z ≤ x^3+y^3+z^3 := by
  have h := mul_nonneg (add_nonneg (add_nonneg hx hy) hz)
    (add_nonneg (add_nonneg (sq_nonneg (x-y)) (sq_nonneg (y-z))) (sq_nonneg (z-x)))
  nlinarith

theorem scaled_triple_young {x y z A B C : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    x*y*z ≤ (A*B*C/3)*(x^3/A^3+y^3/B^3+z^3/C^3) := by
  have h := mul_le_mul_of_nonneg_left
    (triple_young (div_nonneg hx hA.le) (div_nonneg hy hB.le) (div_nonneg hz hC.le))
    (show 0 ≤ A*B*C/3 by positivity)
  have he : (A*B*C/3)*(3*(x/A)*(y/B)*(z/C)) = x*y*z := by field_simp
  simpa only [he, div_pow] using h

theorem absolute_finite_holder {N : ℕ} (hN : 0 < N) (r s t : ℂ)
    {delta K A B C : ℝ} (hd : 0 ≤ delta)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hr : (∫ eta in -delta..delta, ‖Jrho N r eta‖^3) ≤ K*A^3)
    (hs : (∫ eta in -delta..delta, ‖Jrho N s eta‖^3) ≤ K*B^3)
    (ht : (∫ eta in -delta..delta, ‖Jrho N t eta‖^3) ≤ K*C^3) :
    (∫ eta in -delta..delta, ‖tripleKernel N r s t eta‖) ≤ K*A*B*C := by
  have hir := ((Jrho_continuous hN r).norm.pow 3).intervalIntegrable
    (μ := volume) (-delta) delta
  have his := ((Jrho_continuous hN s).norm.pow 3).intervalIntegrable
    (μ := volume) (-delta) delta
  have hit := ((Jrho_continuous hN t).norm.pow 3).intervalIntegrable
    (μ := volume) (-delta) delta
  have hm := intervalIntegral.integral_mono_on (by linarith : -delta ≤ delta)
    ((tripleKernel_integrable hN r s t).norm.intervalIntegrable)
    ((((hir.div_const (A^3)).add (his.div_const (B^3))).add
      (hit.div_const (C^3))).const_mul (A*B*C/3))
    (fun eta _ => by
      simpa only [tripleKernel, norm_mul, charReal_norm, one_mul, Pi.pow_apply] using
        scaled_triple_young (norm_nonneg (Jrho N r eta)) (norm_nonneg (Jrho N s eta))
          (norm_nonneg (Jrho N t eta)) hA hB hC)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hir.div_const _).add (his.div_const _)) (hit.div_const _),
    intervalIntegral.integral_add (hir.div_const _) (his.div_const _),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_div] at hm
  apply hm.trans
  have hr' := div_le_div_of_nonneg_right hr (pow_nonneg hA.le 3)
  have hs' := div_le_div_of_nonneg_right hs (pow_nonneg hB.le 3)
  have ht' := div_le_div_of_nonneg_right ht (pow_nonneg hC.le 3)
  have h := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hr' hs') ht')
    (show 0 ≤ A*B*C/3 by positivity)
  apply h.trans_eq
  field_simp
  ring

theorem finite_holder {N : ℕ} (hN : 0 < N) (r s t : ℂ)
    {delta K A B C : ℝ} (hd : 0 ≤ delta)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hr : (∫ eta in -delta..delta, ‖Jrho N r eta‖^3) ≤ K*A^3)
    (hs : (∫ eta in -delta..delta, ‖Jrho N s eta‖^3) ≤ K*B^3)
    (ht : (∫ eta in -delta..delta, ‖Jrho N t eta‖^3) ≤ K*C^3) :
    ‖finiteMoment N delta r s t‖ ≤ K*A*B*C :=
  (intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := tripleKernel N r s t) (by linarith)).trans
    (absolute_finite_holder hN r s t hd hA hB hC hr hs ht)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
