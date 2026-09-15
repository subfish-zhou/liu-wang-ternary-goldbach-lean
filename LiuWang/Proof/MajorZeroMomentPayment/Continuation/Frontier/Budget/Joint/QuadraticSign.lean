import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint.Consumer

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.SingularIntegral LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint

theorem ramanujan_coprime {N q : ℕ} [NeZero q] (hc : Nat.Coprime N q) :
    ramanujan N q = (ArithmeticFunction.moebius q : ℂ) := by
  rw [ramanujan_integer_formula', Finset.sum_eq_single 1]
  · simp
  · intro d hd hne
    have hn : ¬ d ∣ N := by
      intro hdN
      have h := Nat.dvd_gcd hdN (Nat.dvd_of_mem_divisors hd)
      rw [hc] at h
      exact hne (Nat.dvd_one.mp h)
    simp [hn]
  · intro hn
    exact False.elim (hn (Nat.mem_divisors.mpr ⟨one_dvd q, NeZero.ne q⟩))

theorem gaussScale_sq_even {q : ℕ} [NeZero q] (chi : Character q)
    (hs : chi^2 = 1) (heven : chi (-1) = 1) :
    gaussScale chi^2 = (‖gaussScale chi‖^2 : ℝ) := by
  have hquad := MulChar.isQuadratic_iff_sq_eq_one.mpr hs
  have ht : star (gaussSum chi ZMod.stdAddChar) = gaussSum chi ZMod.stdAddChar := by
    rw [star_gaussSum_eq, hquad.inv, AddChar.inv_mulShift]
    have h := gaussSum_mulShift_eq chi ZMod.stdAddChar (-1 : (ZMod q)ˣ)
    simpa only [Units.coe_neg_one, hquad.inv, heven, one_mul] using h
  have hg : star (gaussScale chi) = gaussScale chi := by
    simp only [gaussScale, hquad.inv, star_mul, star_inv₀, star_natCast, ht]
    ring
  have h := Complex.mul_conj' (gaussScale chi)
  change gaussScale chi * star (gaussScale chi) = _ at h
  simpa only [hg, ← pow_two, ← Complex.ofReal_pow] using h

theorem quadraticCoefficient_even_coprime {N q : ℕ} [NeZero q]
    (hc : Nat.Coprime N q) (chi : Character q) (hs : chi^2 = 1) (heven : chi (-1) = 1) :
    quadraticCoefficient N chi =
      (3*(ArithmeticFunction.moebius q : ℝ)^2*‖gaussScale chi‖^2/(q.totient : ℝ) : ℝ) := by
  rw [quadraticCoefficient, gaussScale_sq_even chi hs heven, principalCoefficient,
    ramanujan_coprime hc]
  push_cast
  ring

theorem quadraticCoefficient_even_nonneg {N q : ℕ} [NeZero q]
    (hc : Nat.Coprime N q) (chi : Character q) (hs : chi^2 = 1) (heven : chi (-1) = 1) :
    0 ≤ (quadraticCoefficient N chi).re ∧ (quadraticCoefficient N chi).im = 0 := by
  rw [quadraticCoefficient_even_coprime hc chi hs heven]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  positivity

theorem actual_quadratic_tail_r24 {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hsmall : (q : ℝ) ≤ sourceP N/32)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ‖fullMoment N 1 rho.re rho.re -
      finiteMoment N (deltaRadius N q) 1 rho.re rho.re‖ ≤
        0.0031*(N : ℝ)^2*baseWeight N rho.re^2 := by
  have hb := (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
  have hu : realEndpoint N rho.re ≤ 1.02*baseWeight N rho.re := by
    have h := exceptional_endpointGap_small hN hr
    unfold endpointGap at h
    linarith
  have htail := actual_radius_tail_real hN (NeZero.pos q) le_rfl hb hb
  have he : realEndpoint N 1 = 1 := by simp [realEndpoint]
  simp only [he, one_mul, Complex.ofReal_one] at htail
  have hratio : (q : ℝ)/sourceP N ≤ 1/32 :=
    (div_le_iff₀ (sourceP_pos hN)).mpr (by linarith)
  have hratio0 : 0 ≤ (q : ℝ)/sourceP N := div_nonneg (Nat.cast_nonneg q) (sourceP_pos hN).le
  have hc : (100 : ℝ)/(3.36^2*Real.pi) ≤ 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  apply htail.trans
  calc
    _ ≤ 3*(1/32 : ℝ)^2*(N : ℝ)^2*
        ((1.02*baseWeight N rho.re)*(1.02*baseWeight N rho.re)) := by
      have hn : 0 ≤ realEndpoint N rho.re := by unfold realEndpoint; positivity
      have hv : 0 ≤ baseWeight N rho.re := by unfold baseWeight; positivity
      gcongr
    _ ≤ _ := by nlinarith [sq_nonneg ((N : ℝ)*baseWeight N rho.re)]

theorem actual_quadratic_moment_r24 {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hsmall : (q : ℝ) ≤ sourceP N/32)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    0.4939*(N : ℝ)^2*baseWeight N rho.re^2 ≤
      (finiteMoment N (deltaRadius N q) 1 rho.re rho.re).re := by
  have hb := (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
  have hm := (realMass_bounds (nat_pos_of_exp_le hN) le_rfl hb hb).1
  have ht := (Complex.re_le_norm (fullMoment N 1 rho.re rho.re -
      finiteMoment N (deltaRadius N q) 1 rho.re rho.re)).trans (actual_quadratic_tail_r24 hN hsmall hr)
  have hf := fullMoment_real (nat_pos_of_exp_le hN) 1 rho.re rho.re
  simp only [Complex.ofReal_one] at hf
  rw [hf, Complex.sub_re, Complex.ofReal_re] at ht
  have hw : baseWeight N 1 = 1 := by simp [baseWeight]
  simp only [hw, one_mul] at hm
  nlinarith [sq_nonneg ((N : ℝ)*baseWeight N rho.re)]

theorem actual_even_quadratic_credit {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hsmall : (q : ℝ) ≤ sourceP N/32)
    (hc : Nat.Coprime N q) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ exceptionalValues N chi) (heven : chi (-1) = 1) :
    0.4939*(N : ℝ)^2*baseWeight N rho.re^2*(quadraticCoefficient N chi).re ≤
      (quadraticCoefficient N chi*finiteMoment N (deltaRadius N q) 1 rho.re rho.re).re := by
  have hq : (q : ℝ) ≤ sourceP N := by linarith [sourceP_pos hN]
  have hs := (exceptionalValues_quadratic_simple hN hq hr).2.1
  have hb := quadraticCoefficient_even_nonneg hc chi hs heven
  rw [Complex.mul_re, hb.2, zero_mul, sub_zero]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (actual_quadratic_moment_r24 hN hsmall hr) hb.1

def evenQuadraticPayment {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) (beta : ℝ) : ℝ :=
  paidLower N (deltaRadius N q) beta 0 (linearCoefficient N chi) 0 (cubicCoefficient N chi) +
    0.4939*(N : ℝ)^2*baseWeight N beta^2*(quadraticCoefficient N chi).re

theorem evenQuadraticPayment_lower {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hsmall : (q : ℝ) ≤ sourceP N/32)
    (hc : Nat.Coprime N q) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ exceptionalValues N chi) (heven : chi (-1) = 1) :
    evenQuadraticPayment N chi rho.re ≤ (exceptionalArc N q).re := by
  have hq : (q : ℝ) ≤ sourceP N := by linarith [sourceP_pos hN]
  have hb := (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
  have hm := jointFinite_re_lower (nat_pos_of_exp_le hN) hb (deltaRadius_pos hN (NeZero.pos q))
    0 (linearCoefficient N chi) 0 (cubicCoefficient N chi)
  have he : exceptionalArc N q =
      jointFinite N (deltaRadius N q) rho.re 0 (linearCoefficient N chi) 0 (cubicCoefficient N chi) +
      quadraticCoefficient N chi*finiteMoment N (deltaRadius N q) 1 rho.re rho.re := by
    rw [exceptionalArc_eq_joint hN hq hr]
    unfold jointFinite
    ring
  rw [he, Complex.add_re]
  exact add_le_add hm (actual_even_quadratic_credit hN hsmall hc hr heven)

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint
