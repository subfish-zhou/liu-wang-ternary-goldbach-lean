import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint.CrossPhase

set_option autoImplicit false
noncomputable section
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion
open LiuWang.Proof.SingularIntegral LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint

theorem realDefect_smooth {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1) (eta : ℝ) :
    ‖realDefect N beta eta‖*(1+Real.pi*(N : ℝ)*|eta|) ≤
      2*(N : ℝ)*endpointGap N beta := by
  have hm := realDefect_mass hN hb eta
  by_cases he : eta = 0
  · subst eta
    simpa using hm.trans (by nlinarith [endpointGap_nonneg hN hb] :
      (N : ℝ)*endpointGap N beta ≤ 2*(N : ℝ)*endpointGap N beta)
  have hr := (le_div_iff₀ (mul_pos Real.pi_pos (abs_pos.mpr he))).mp
    (realDefect_reciprocal hN hb he)
  nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) N)]

def mixedEnvelope (N : ℕ) (beta : ℝ) (U V : ℂ) : ℝ :=
  ‖U*(baseWeight N beta : ℂ)+V*(baseWeight N beta : ℂ)^2‖ +
    ‖U+2*V*(baseWeight N beta : ℂ)‖*endpointGap N beta +
    ‖V‖*(endpointGap N beta)^2

theorem mixedEnvelope_nonneg {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1) (U V : ℂ) :
    0 ≤ mixedEnvelope N beta U V := by
  unfold mixedEnvelope
  have := endpointGap_nonneg hN hb
  positivity

theorem mixed_pair_smooth {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (U V : ℂ) (eta : ℝ) :
    ‖U*J N eta*Jrho N beta eta + V*(Jrho N beta eta)^2‖ ≤
      4*(N : ℝ)^2*mixedEnvelope N beta U V/(1+Real.pi*(N : ℝ)*|eta|)^2 := by
  let d := 1+Real.pi*(N : ℝ)*|eta|
  have hd : 0 < d := by dsimp [d]; positivity
  have hw := endpointGap_nonneg hN hb
  have hj : ‖J N eta‖ ≤ 2*(N : ℝ)/d := (le_div_iff₀ hd).mpr (J_smooth_decay hN eta)
  have he : ‖realDefect N beta eta‖ ≤ 2*(N : ℝ)*endpointGap N beta/d :=
    (le_div_iff₀ hd).mpr (realDefect_smooth hN hb eta)
  have hid : U*J N eta*Jrho N beta eta + V*(Jrho N beta eta)^2 =
      (U*(baseWeight N beta : ℂ)+V*(baseWeight N beta : ℂ)^2)*(J N eta)^2 +
        (U+2*V*(baseWeight N beta : ℂ))*J N eta*realDefect N beta eta +
        V*(realDefect N beta eta)^2 := by unfold realDefect; ring
  rw [hid]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ ‖U*(baseWeight N beta : ℂ)+V*(baseWeight N beta : ℂ)^2‖*(2*(N : ℝ)/d)^2 +
        ‖U+2*V*(baseWeight N beta : ℂ)‖*(2*(N : ℝ)/d)*
          (2*(N : ℝ)*endpointGap N beta/d) +
        ‖V‖*(2*(N : ℝ)*endpointGap N beta/d)^2 := by gcongr
    _ = _ := by unfold mixedEnvelope; dsimp [d]; field_simp; ring

theorem mixed_kernel_direct {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    {rho : ℂ} (hr : 0 ≤ rho.re) (hr0 : rho ≠ 0) (U V : ℂ) (eta : ℝ) :
    ‖U*tripleKernel N 1 beta rho eta + V*tripleKernel N beta beta rho eta‖ ≤
      8*(N : ℝ)^2*(N : ℝ)^rho.re*mixedEnvelope N beta U V /
        (‖rho‖*(1+Real.pi*(N : ℝ)*|eta|)) := by
  let d := 1+Real.pi*(N : ℝ)*|eta|
  have hd : 0 < d := by dsimp [d]; positivity
  have hz : ‖Jrho N rho eta‖ ≤ 2*(N : ℝ)^rho.re*d/‖rho‖ := by
    apply (le_div_iff₀ (norm_pos_iff.mpr hr0)).mpr
    simpa only [d, mul_comm] using Jrho_norm_mul_rho hN hr eta
  have he : U*tripleKernel N 1 beta rho eta + V*tripleKernel N beta beta rho eta =
      (U*J N eta*Jrho N beta eta+V*(Jrho N beta eta)^2)*Jrho N rho eta*
        charReal (-(N : ℝ)*eta) := by simp only [tripleKernel, Jrho_one_eq_J]; ring
  rw [he, norm_mul, norm_mul, charReal_norm, mul_one]
  apply (mul_le_mul (mixed_pair_smooth hN hb U V eta) hz (norm_nonneg _)
    (by have := mixedEnvelope_nonneg hN hb U V; positivity)).trans_eq
  dsimp [d]
  field_simp
  ring

theorem mixedMoment_direct {N : ℕ} (hN : 0 < N) {beta delta : ℝ}
    (hb : beta ≤ 1) (hd : 0 ≤ delta) {rho : ℂ} (hr : 0 ≤ rho.re) (hr0 : rho ≠ 0)
    (U V : ℂ) :
    ‖U*finiteMoment N delta 1 beta rho + V*finiteMoment N delta beta beta rho‖ ≤
      directMomentBound N delta rho*mixedEnvelope N beta U V := by
  have he : U*finiteMoment N delta 1 beta rho + V*finiteMoment N delta beta beta rho =
      ∫ eta in -delta..delta,
        U*tripleKernel N 1 beta rho eta + V*tripleKernel N beta beta rho eta := by
    rw [intervalIntegral.integral_add
      (((continuous_tripleKernel hN 1 beta rho).const_mul U).intervalIntegrable _ _)
      (((continuous_tripleKernel hN beta beta rho).const_mul V).intervalIntegrable _ _)]
    simp only [finiteMoment, intervalIntegral.integral_const_mul]
  rw [he]
  have hc : 0 < Real.pi*(N : ℝ) := by positivity
  let K := 8*(N : ℝ)^2*(N : ℝ)^rho.re*mixedEnvelope N beta U V/‖rho‖
  have hg : Continuous (fun eta : ℝ => K*(1/(1+Real.pi*(N : ℝ)*|eta|))) :=
    continuous_const.mul (continuous_const.div
      (continuous_const.add (continuous_const.mul continuous_abs)) (fun _ => by positivity))
  have hm := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -delta ≤ delta)
    (μ := volume)
    (f := fun eta => U*tripleKernel N 1 beta rho eta+V*tripleKernel N beta beta rho eta)
    (g := fun eta => K*(1/(1+Real.pi*(N : ℝ)*|eta|)))
    (Filter.Eventually.of_forall fun eta _ =>
      (mixed_kernel_direct hN hb hr hr0 U V eta).trans_eq
        (by dsimp [K]; rw [div_mul_eq_div_div]; ring))
    (hg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, integral_smooth_reciprocal hc hd] at hm
  apply hm.trans_eq
  have hp : (N : ℝ)^rho.re = baseWeight N rho.re*(N : ℝ) := by
    rw [baseWeight, ← Real.rpow_add_one (Nat.cast_pos.mpr hN).ne']
    congr 1
    ring
  dsimp [K]
  rw [hp]
  unfold directMomentBound
  field_simp
  ring

theorem mixedMoment_actual {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {beta : ℝ} (hb : beta ≤ 1) {rho : ℂ} (hr : 0 ≤ rho.re) (hr0 : rho ≠ 0)
    (U V : ℂ) :
    ‖U*finiteMoment N (deltaRadius N q) 1 beta rho +
      V*finiteMoment N (deltaRadius N q) beta beta rho‖ ≤
      (16/Real.pi)*(N : ℝ)^2*radiusLog N q*
        (baseWeight N rho.re/‖rho‖)*mixedEnvelope N beta U V := by
  simpa only [actual_directMomentBound hN hq] using
    mixedMoment_direct (nat_pos_of_exp_le hN) hb (deltaRadius_pos hN hq).le hr hr0 U V

theorem mixedEnvelope_r24 {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ exceptionalValues N chi) (U V : ℂ) :
    mixedEnvelope N rho.re U V ≤
      ‖U*(baseWeight N rho.re : ℂ)+V*(baseWeight N rho.re : ℂ)^2‖ +
        ‖U+2*V*(baseWeight N rho.re : ℂ)‖*(0.02*baseWeight N rho.re) +
        ‖V‖*(0.02*baseWeight N rho.re)^2 := by
  have hw := exceptional_endpointGap_small hN hr
  have hp := endpointGap_nonneg (nat_pos_of_exp_le hN)
    (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
  unfold mixedEnvelope
  gcongr

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint
