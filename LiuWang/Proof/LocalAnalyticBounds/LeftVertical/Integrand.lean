import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.GammaBounds
import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.RightLineBound
import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.Integral
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLeftLineReflection
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLeftLineNonvanishing

/-!
# 原被积函数在实际左线上的衰减与连续性

复用 `horizontalIntegrand`，端点为实数 `t` 和 `2.5`。
非零性独立来自左线生产者，覆盖 `u = 0`，不使用水平高度分离。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical

theorem norm_logDeriv_LFunction_left_le
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex} (hs : s.re = -(1 : Real) / 2) :
    ‖logDeriv chi.LFunction s‖ ≤ Real.log q + Real.log (|s.im| + 2) + 40 := by
  have hqone : (1 : Real) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hqlog := Real.log_nonneg hqone
  have hr : (1 - s).re = (3 : Real) / 2 := by simp [hs]; ring
  have hL := norm_logDeriv_LFunction_three_halves_le_twenty (Inv.inv chi) hr
  have hGr := norm_logDeriv_gammaFactor_three_halves_le (Inv.inv chi) hr
  have hGl := norm_logDeriv_gammaFactor_left_le chi hs
  simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hGr
  rw [logDeriv_LFunction_left_line_eq_reflected hchi hPrimitive hs]
  calc
    _ ≤ ((‖-(Real.log q : Complex)‖ +
        ‖logDeriv (Inv.inv chi).LFunction (1 - s)‖) +
        ‖logDeriv (Inv.inv chi).gammaFactor (1 - s)‖) +
        ‖logDeriv chi.gammaFactor s‖ :=
      (norm_sub_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ Real.log q + Real.log (|s.im| + 2) + 40 := by
      simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hqlog]
      linarith

theorem rpow_neg_half_le_inv {x a : Real} (hx : 0 ≤ x) (ha : 0 < a)
    (hax : a ^ 2 ≤ x) : x ^ (-(1 : Real) / 2) ≤ a⁻¹ := by
  have hs : a ≤ Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
  rw [show -(1 : Real) / 2 = -(1 / 2 : Real) by ring, Real.rpow_neg hx,
    ← Real.sqrt_eq_rpow]
  exact inv_anti₀ ha hs

theorem norm_real_centered_kernel_left_le {t : Real} (ht : 9 ≤ t)
    {s : Complex} (hs : s.re = -(1 : Real) / 2) :
    ‖((t : Complex) ^ s - (2.5 : Complex) ^ s) / s‖ ≤ 3 / (|s.im| + 1) := by
  have ht0 : 0 < t := by linarith
  have htp : ‖(t : Complex) ^ s‖ ≤ (1 : Real) / 3 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, hs]
    exact (rpow_neg_half_le_inv ht0.le (by norm_num : (0 : Real) < 3)
      (by linarith)).trans (by norm_num)
  have hcp : ‖(2.5 : Complex) ^ s‖ ≤ (2 : Real) / 3 := by
    rw [show (2.5 : Complex) = ((2.5 : Real) : Complex) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), hs]
    exact (rpow_neg_half_le_inv (by norm_num : (0 : Real) ≤ 2.5)
      (by norm_num : (0 : Real) < 3 / 2) (by norm_num)).trans (by norm_num)
  have hnum : ‖(t : Complex) ^ s - (2.5 : Complex) ^ s‖ ≤ 1 :=
    (norm_sub_le _ _).trans (by linarith)
  have hr : (1 : Real) / 2 ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    norm_num [hs] at h ⊢
    exact h
  have hi := Complex.abs_im_le_norm s
  have hthird : (|s.im| + 1) / 3 ≤ ‖s‖ := by linarith
  rw [norm_div]
  calc
    _ ≤ 1 / ‖s‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ 1 / ((|s.im| + 1) / 3) :=
      one_div_le_one_div_of_le (by positivity) hthird
    _ = 3 / (|s.im| + 1) := by field_simp

theorem norm_horizontalIntegrand_left_le
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (ht : 9 ≤ t) {s : Complex} (hs : s.re = -(1 : Real) / 2) :
    ‖HorizontalEstimate.horizontalIntegrand chi t s‖ ≤
      3 * (Real.log q + Real.log (|s.im| + 2) + 40) / (|s.im| + 1) := by
  have hlog := norm_logDeriv_LFunction_left_le hchi hPrimitive hs
  have hkernel := norm_real_centered_kernel_left_le ht hs
  rw [HorizontalEstimate.horizontalIntegrand, mul_div_assoc, norm_mul, norm_neg]
  exact (mul_le_mul hlog hkernel (norm_nonneg _)
    ((norm_nonneg _).trans hlog)).trans_eq (by ring)

theorem continuous_left_integrand
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (ht : 0 < t) :
    Continuous (fun u : Real => HorizontalEstimate.horizontalIntegrand chi t
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I)) := by
  have hL := DirichletCharacter.differentiable_LFunction hchi
  have hpath : Continuous (fun u : Real => (-1 / 2 : Complex) + (u : Complex) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  apply continuous_iff_continuousAt.mpr
  intro u
  have hs : ((-1 / 2 : Complex) + (u : Complex) * Complex.I).re = -(1 : Real) / 2 := by
    norm_num
  have hn := LFunction_ne_zero_of_re_eq_neg_one_half hchi hPrimitive hs
  have hs0 : (-1 / 2 : Complex) + (u : Complex) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hld : ContinuousAt (logDeriv chi.LFunction)
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I) := by
    change ContinuousAt (fun z : Complex => deriv chi.LFunction z / chi.LFunction z) _
    exact (hL.contDiff.continuous_deriv le_rfl).continuousAt.div hL.continuous.continuousAt hn
  have hc : ContinuousAt (HorizontalEstimate.horizontalIntegrand chi t)
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I) := by
    change ContinuousAt (fun z : Complex =>
      (-logDeriv chi.LFunction z) * ((t : Complex) ^ z - (2.5 : Complex) ^ z) / z) _
    apply (hld.neg.mul _).div continuousAt_id hs0
    have htC : NeZero (t : Complex) := ⟨Complex.ofReal_ne_zero.mpr ht.ne'⟩
    have hcC : NeZero (2.5 : Complex) := ⟨by norm_num⟩
    exact (continuous_const_cpow (t : Complex)).continuousAt.sub
      (continuous_const_cpow (2.5 : Complex)).continuousAt
  exact hc.comp (x := u) hpath.continuousAt

theorem intervalIntegrable_left_integrand
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (ht : 0 < t) (Hminus Hplus : Real) :
    IntervalIntegrable (fun u : Real => HorizontalEstimate.horizontalIntegrand chi t
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I)) volume Hminus Hplus :=
  (continuous_left_integrand hchi hPrimitive ht).intervalIntegrable _ _

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical
