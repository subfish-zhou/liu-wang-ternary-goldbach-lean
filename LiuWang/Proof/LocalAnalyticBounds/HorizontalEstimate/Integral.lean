import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.LogDerivative
import LiuWang.Proof.Parameters.Main
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# 真实水平被积函数与源域参数

端点为实数 `t` 与原文的 `2.5`。证明被积函数连续，排除不可积时
积分定义为零的退化；`SplitIntegral` 消费这些结果，实际分段积分。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

def horizontalIntegrand {q : Nat} [NeZero q]
    (chi : Character q) (t : Real) (s : Complex) : Complex :=
  (-logDeriv chi.LFunction s) * ((t : Complex) ^ s - (2.5 : Complex) ^ s) / s

theorem source_horizontal_parameters {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {t : Real}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    (2000 : Real) ^ (15 : Nat) ≤ sourceT N ∧
      200000 ≤ t ∧ 1990 ≤ Real.log t ∧ Real.log t ≤ sourceL N ∧
      1 ≤ 1 + 1 / sourceL N ∧ 1 + 1 / sourceL N ≤ 3 / 2 ∧
      t ^ (1 + 1 / sourceL N) ≤ 3 * t := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hT : (2000 : Real) ^ (15 : Nat) ≤ sourceT N := by
    unfold sourceT
    gcongr
  have htT := sourceT_lt_real_endpoint hN htlo
  have htbig : 200000 ≤ t := by
    have hh : (200000 : Real) ≤ 2000 ^ (15 : Nat) := by norm_num
    linarith
  have ht0 : 0 < t := by linarith
  have hNu : (N : Real) ≤ 1000 * t := by
    change (N : Real) / 1000 ≤ t at htlo
    linarith
  have hlog : sourceL N ≤ Real.log 1000 + Real.log t := by
    have h := Real.log_le_log (natCast_pos_of_exp_le hN) hNu
    rwa [Real.log_mul (by norm_num) ht0.ne'] at h
  have h1000 : Real.log 1000 ≤ 10 := by
    have h := Real.log_le_log (by norm_num : (0 : Real) < 1000)
      (by norm_num : (1000 : Real) ≤ 2 ^ (10 : Nat))
    rw [Real.log_pow] at h
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h hh
    linarith
  have hloglo : 1990 ≤ Real.log t := by linarith
  have hloghi : Real.log t ≤ sourceL N := Real.log_le_log ht0 hthi
  have hb0 : 0 ≤ 1 / sourceL N := by positivity
  have hbu : 1 / sourceL N ≤ (1 : Real) / 2 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have htbound : t ^ (1 + 1 / sourceL N) ≤ 3 * t := by
    rw [Real.rpow_add ht0, Real.rpow_one, Real.rpow_def_of_pos ht0]
    have he : Real.log t * (1 / sourceL N) ≤ 1 := by
      rw [mul_one_div]
      exact (div_le_one hL0).mpr hloghi
    have hx := (Real.exp_le_exp.mpr he).trans Real.exp_one_lt_three.le
    nlinarith
  exact ⟨hT, htbig, hloglo, hloghi, by linarith, by linarith, htbound⟩

theorem continuousOn_horizontalIntegrand
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t H B b : Real} (ht : 0 < t) (hB : 0 < B) (hH : H ≠ 0)
    (hsep : ∀ p : CompletedZeroIndex chi, B⁻¹ ≤ |(completedZeroValue p).im - H|) :
    ContinuousOn (fun σ : Real => horizontalIntegrand chi t
      ((σ : Complex) + (H : Complex) * Complex.I)) (Set.Icc (-(1 : Real) / 2) b) := by
  have hL := DirichletCharacter.differentiable_LFunction hchi
  have hpath : Continuous (fun σ : Real => (σ : Complex) + (H : Complex) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  intro σ hσ
  have hlo : -(1 : Real) / 2 ≤ ((σ : Complex) + (H : Complex) * Complex.I).re := by
    simpa using hσ.1
  have hn := LFunction_ne_zero_on_separated_strip hchi hPrimitive hB hH hsep
    (s := (σ : Complex) + (H : Complex) * Complex.I) (by simp) hlo
  have hs0 : (σ : Complex) + (H : Complex) * Complex.I ≠ 0 := by
    intro hh
    apply hH
    simpa using congrArg Complex.im hh
  have hld : ContinuousAt (logDeriv chi.LFunction)
      ((σ : Complex) + (H : Complex) * Complex.I) := by
    change ContinuousAt (fun z : Complex => deriv chi.LFunction z / chi.LFunction z) _
    exact (hL.contDiff.continuous_deriv le_rfl).continuousAt.div hL.continuous.continuousAt hn
  have hc : ContinuousAt (horizontalIntegrand chi t)
      ((σ : Complex) + (H : Complex) * Complex.I) := by
    change ContinuousAt (fun z : Complex =>
      (-logDeriv chi.LFunction z) * ((t : Complex) ^ z - (2.5 : Complex) ^ z) / z) _
    apply (hld.neg.mul _).div continuousAt_id hs0
    have htC : NeZero (t : Complex) := ⟨Complex.ofReal_ne_zero.mpr ht.ne'⟩
    have hcC : NeZero (2.5 : Complex) := ⟨by norm_num⟩
    exact (continuous_const_cpow (t : Complex)).continuousAt.sub
      (continuous_const_cpow (2.5 : Complex)).continuousAt
  exact (hc.comp (f := fun x : Real => (x : Complex) + (H : Complex) * Complex.I)
    (x := σ) hpath.continuousAt).continuousWithinAt

theorem norm_horizontalIntegrand_le_power
    {q : Nat} [NeZero q] (chi : Character q) {t D : Real} {s : Complex}
    (ht : 0 < t) (hs : s.re ≤ 2) (him : 0 < |s.im|)
    (hlog : ‖logDeriv chi.LFunction s‖ ≤ D) :
    ‖horizontalIntegrand chi t s‖ ≤ D / |s.im| * (t ^ s.re + 7) := by
  have hD : 0 ≤ D := (norm_nonneg _).trans hlog
  have hcp : ‖(t : Complex) ^ s - (2.5 : Complex) ^ s‖ ≤ t ^ s.re + 7 := by
    have hc : ‖(2.5 : Complex) ^ s‖ ≤ 7 := by
      rw [show (2.5 : Complex) = ((2.5 : Real) : Complex) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2.5) hs
      norm_num at h
      linarith
    have hp := Complex.norm_cpow_eq_rpow_re_of_pos ht s
    exact (norm_sub_le _ _).trans (by rw [hp]; linarith)
  rw [horizontalIntegrand, norm_div, norm_mul, norm_neg]
  calc
    _ ≤ D * (t ^ s.re + 7) / ‖s‖ :=
      div_le_div_of_nonneg_right (mul_le_mul hlog hcp (norm_nonneg _) hD) (norm_nonneg _)
    _ ≤ D * (t ^ s.re + 7) / |s.im| :=
      div_le_div_of_nonneg_left (by positivity) him (Complex.abs_im_le_norm s)
    _ = _ := by ring

end LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
