import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.DirectKernel

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularIntegral LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier

theorem integral_smooth_reciprocal {c delta : ℝ} (hc : 0 < c) (hd : 0 ≤ delta) :
    (∫ eta in -delta..delta, 1 / (1 + c*|eta|)) = 2/c * Real.log (1+c*delta) := by
  have hf : Continuous (fun eta : ℝ => 1 / (1+c*|eta|)) :=
    continuous_const.div (continuous_const.add (continuous_const.mul continuous_abs))
      (fun eta => ne_of_gt (by positivity))
  have hi : (∫ eta in (0 : ℝ)..delta, 1/(1+c*eta)) = Real.log (1+c*delta)/c := by
    have hcont : ContinuousOn (fun eta : ℝ => 1/(1+c*eta)) (Icc 0 delta) :=
      continuousOn_const.div (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
        (fun eta he => ne_of_gt (by nlinarith [he.1]))
    have hderiv : ∀ eta ∈ uIcc (0 : ℝ) delta,
        HasDerivAt (fun eta : ℝ => Real.log (1+c*eta)/c) (1/(1+c*eta)) eta := by
      intro eta he
      rw [uIcc_of_le hd] at he
      have hpos : 0 < 1+c*eta := by nlinarith [he.1]
      convert ((((hasDerivAt_id eta).const_mul c).const_add 1).log hpos.ne').div_const c using 1 <;>
        first | rfl | (dsimp; field_simp)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable_of_Icc hd)
    simpa using h
  have hi' : (∫ eta in (0 : ℝ)..delta, 1/(1+c*|eta|)) = Real.log (1+c*delta)/c := by
    rw [← hi]
    apply intervalIntegral.integral_congr
    intro eta he
    rw [uIcc_of_le hd] at he
    dsimp only
    rw [abs_of_nonneg he.1]
  have he : (∫ eta in -delta..(0 : ℝ), 1/(1+c*|eta|)) =
      ∫ eta in (0 : ℝ)..delta, 1/(1+c*|eta|) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun eta : ℝ => 1/(1+c*|eta|)) (a := 0) (b := delta)
    simpa only [abs_neg, neg_zero] using h.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-delta) 0) (hf.intervalIntegrable 0 delta), he, hi']
  ring

def directMomentBound (N : ℕ) (delta : ℝ) (rho : ℂ) : ℝ :=
  (16 / Real.pi) * (N : ℝ)^2 * baseWeight N rho.re *
    Real.log (1 + Real.pi * (N : ℝ) * delta) / ‖rho‖

theorem finiteMoment_direct {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hb : 0 ≤ rho.re) (hr : rho ≠ 0) {delta : ℝ} (hd : 0 ≤ delta) :
    ‖finiteMoment N delta 1 1 rho‖ ≤ directMomentBound N delta rho := by
  have hc : 0 < Real.pi * (N : ℝ) := mul_pos Real.pi_pos (Nat.cast_pos.mpr hN)
  have hg : Continuous (fun eta : ℝ =>
      (8*(N : ℝ)^2*(N : ℝ)^rho.re/‖rho‖) * (1/(1+Real.pi*(N : ℝ)*|eta|))) :=
    continuous_const.mul (continuous_const.div
      (continuous_const.add (continuous_const.mul continuous_abs)) (fun eta => by positivity))
  have hm := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -delta ≤ delta)
    (μ := volume)
    (f := tripleKernel N 1 1 rho)
    (g := fun eta => (8*(N : ℝ)^2*(N : ℝ)^rho.re/‖rho‖) * (1/(1+Real.pi*(N : ℝ)*|eta|)))
    (Filter.Eventually.of_forall fun eta _ => (linear_kernel_direct hN hb hr eta).trans_eq
      (by rw [div_mul_eq_div_div]; ring))
    (hg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, integral_smooth_reciprocal hc hd] at hm
  apply hm.trans_eq
  have hp : (N : ℝ)^rho.re = baseWeight N rho.re * (N : ℝ) := by
    rw [baseWeight, ← Real.rpow_add_one (Nat.cast_pos.mpr hN).ne']
    congr 1
    ring
  rw [hp]
  unfold directMomentBound
  field_simp
  ring

theorem finiteMoment_direct_zero (N : ℕ) (rho : ℂ) :
    finiteMoment N 0 1 1 rho = 0 ∧ directMomentBound N 0 rho = 0 := by
  simp [finiteMoment, directMomentBound]

def radiusLog (N q : ℕ) : ℝ := Real.log (1 + 0.336 * sourceP N / (q : ℝ))

theorem actual_directMomentBound {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : 0 < q) (rho : ℂ) :
    directMomentBound N (deltaRadius N q) rho =
      (16/Real.pi) * (N : ℝ)^2 * radiusLog N q * (baseWeight N rho.re / ‖rho‖) := by
  have he : Real.pi * (N : ℝ) * deltaRadius N q = 0.336 * sourceP N / (q : ℝ) := by
    unfold deltaRadius
    have hn := (nat_pos_of_exp_le hN)
    have hn' : (N : ℝ) ≠ 0 := by positivity
    have hq' : (q : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  unfold directMomentBound radiusLog
  rw [he]
  ring

theorem actual_finiteMoment_direct {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : 0 < q) {rho : ℂ} (hb : 0 ≤ rho.re) (hr : rho ≠ 0) :
    ‖finiteMoment N (deltaRadius N q) 1 1 rho‖ ≤
      (16/Real.pi) * (N : ℝ)^2 * radiusLog N q * (baseWeight N rho.re / ‖rho‖) := by
  simpa only [actual_directMomentBound hN hq] using
    finiteMoment_direct (nat_pos_of_exp_le hN) hb hr (deltaRadius_pos hN hq).le

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier
