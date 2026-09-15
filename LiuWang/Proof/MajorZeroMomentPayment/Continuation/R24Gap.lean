import LiuWang.Proof.MajorZeroMomentPayment.Continuation.AllModuli

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation

theorem sourceP_log_ge_twenty {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    20 ≤ Real.log (sourceP N) := by
  have hl := sourceL_ge_2000 hN
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1024)
    (by linarith : (1024 : ℝ) ≤ sourceL N)
  have he : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2^10 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  rw [sourceP, Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9]

theorem exceptional_endpointGap_small {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    endpointGap N rho.re ≤ 0.02 * baseWeight N rho.re := by
  have hreg := (Finset.mem_filter.mp hr).2
  have hz := mem_zeroValues.mp (Finset.mem_filter.mp hr).1
  have hg0 : 0 ≤ 1 - rho.re := by linarith [hz.2.2.1]
  have hlog := sourceP_log_ge_twenty hN
  have hg : 1 - rho.re ≤ 1/480 := by
    have hdiv : 1 / (24 * Real.log (sourceP N)) ≤ (1/480 : ℝ) := by
      apply (div_le_iff₀ (by linarith : 0 < 24 * Real.log (sourceP N))).mpr
      linarith
    linarith [hreg.1]
  have hlog1000 : Real.log (1000 : ℝ) ≤ 7 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1000)
      (by norm_num : (1000 : ℝ) ≤ 2^10)
    rw [Real.log_pow] at h
    norm_num at h
    linarith [Real.log_two_lt_d9]
  have hsmalllog : Real.log (0.001 : ℝ) = -Real.log 1000 := by
    rw [show (0.001 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hprod : Real.log (0.001 : ℝ) * (rho.re - 1) ≤ Real.log (1.02 : ℝ) := by
    have hmul := mul_le_mul hlog1000 hg hg0 (by norm_num : (0 : ℝ) ≤ 7)
    have hone := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 1.02)
    rw [hsmalllog]
    norm_num at hone
    nlinarith
  have hrpow : (0.001 : ℝ)^(rho.re - 1) ≤ 1.02 := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact (Real.exp_le_exp.mpr hprod).trans_eq (Real.exp_log (by norm_num))
  have hv : 0 ≤ baseWeight N rho.re := by unfold baseWeight; positivity
  have hm := mul_le_mul_of_nonneg_right hrpow hv
  unfold endpointGap realEndpoint
  rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)]
  change (0.001 : ℝ)^(rho.re - 1) * baseWeight N rho.re - baseWeight N rho.re ≤ _
  nlinarith

theorem shiftedEnvelope_mono_gap {v w z : ℝ} (hw : 0 ≤ w) (hwz : w ≤ z)
    (D A B C : ℂ) :
    shiftedEnvelope v w D A B C ≤ shiftedEnvelope v z D A B C := by
  unfold shiftedEnvelope
  gcongr

theorem allModuliPayment_r24_budget {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    -0.955 * (N : ℝ)^2 *
      shiftedEnvelope (baseWeight N rho.re) (0.02 * baseWeight N rho.re) 0
        (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi) ≤
      allModuliExceptionalPayment N q := by
  have hz := mem_zeroValues.mp (Finset.mem_filter.mp hr).1
  have hm := shiftedEnvelope_mono_gap (v := baseWeight N rho.re)
    (endpointGap_nonneg (nat_pos_of_exp_le hN) hz.2.2.1.le)
    (exceptional_endpointGap_small hN hr) (0 : ℂ)
    (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi)
  have hp := mul_le_mul_of_nonpos_left hm
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-0.955 : ℝ) ≤ 0) (sq_nonneg (N : ℝ)))
  apply hp.trans
  rw [← shiftedExceptionalPayment_at_witness hN hq hr]
  exact le_max_right _ _

theorem exceptionalArc_r24_budget {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    -0.955 * (N : ℝ)^2 *
      shiftedEnvelope (baseWeight N rho.re) (0.02 * baseWeight N rho.re) 0
        (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi) ≤
      (exceptionalArc N q).re :=
  (allModuliPayment_r24_budget hN hq hr).trans (allModuliExceptionalPayment_lower hN hq)

end LiuWang.Proof.MajorZeroMomentPayment.Continuation
