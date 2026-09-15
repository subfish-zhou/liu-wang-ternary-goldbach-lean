import LiuWang.Proof.MajorZeroMomentPayment.Exceptional

/-! An actual arithmetic class with a favorable quadratic contribution:
an even quadratic character at a prime not dividing N. Its positive coefficient
is proved by the Gauss-square identity, not assumed, and the finite moment
is paid before its credit is inserted into the count. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment

theorem gaussScale_sq_prime_even {p : ℕ} [NeZero p] (hp : p.Prime)
    (chi : Character p) (hc : chi ≠ 1) (hs : chi^2 = 1)
    (heven : chi (-1) = 1) :
    gaussScale chi^2 = ((p : ℝ) / (p.totient : ℝ)^2 : ℝ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hquad := MulChar.isQuadratic_iff_sq_eq_one.mpr hs
  have ht := gaussSum_sq hc hquad (ZMod.isPrimitive_stdAddChar p)
  rw [heven, one_mul, ZMod.card] at ht
  rw [gaussScale, hquad.inv, mul_pow, ht]
  push_cast
  ring

theorem quadraticCoefficient_prime_even {p : ℕ} [NeZero p] (hp : p.Prime)
    {N : ℕ} (hn : ¬ p ∣ N) (chi : Character p) (hc : chi ≠ 1)
    (hs : chi^2 = 1) (heven : chi (-1) = 1) :
    quadraticCoefficient N chi = (3 * (p : ℝ) / (p.totient : ℝ)^3 : ℝ) := by
  rw [quadraticCoefficient, gaussScale_sq_prime_even hp chi hc hs heven,
    principalCoefficient, ArithmeticFunction.moebius_apply_prime hp,
    ramanujan_prime N hp, if_neg hn]
  push_cast
  ring

theorem quadratic_tail_small {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    (hsmall : (q : ℝ) ≤ sourceP N / 1000) {beta : ℝ}
    (hb : 1/2 ≤ beta ∧ beta ≤ 1) :
    ‖fullMoment N 1 beta beta - finiteMoment N (deltaRadius N q) 1 beta beta‖ ≤
      0.0031 * (N : ℝ)^2 * baseWeight N beta^2 := by
  have hP := sourceP_pos hN
  have hratio : (q : ℝ) / sourceP N ≤ 1/1000 :=
    (div_le_iff₀ hP).mpr (by linarith)
  have hratio0 : 0 ≤ (q : ℝ) / sourceP N := by positivity
  have hc : (100 : ℝ) / (3.36^2 * Real.pi) ≤ 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have htail := actual_radius_tail_real hN hq (r := 1) (s := beta) (t := beta)
    le_rfl hb.2 hb.2
  have he : realEndpoint N 1 = 1 := by simp [realEndpoint]
  simp only [he, one_mul, Complex.ofReal_one] at htail
  apply htail.trans
  calc
    _ ≤ 3 * (1/1000 : ℝ)^2 * (N : ℝ)^2 *
        ((32 * baseWeight N beta) * (32 * baseWeight N beta)) := by
      apply mul_le_mul _ (mul_self_le_mul_self (by unfold realEndpoint; positivity)
        (endpoint_le_thirtytwo hb.1)) (by unfold realEndpoint; positivity) (by positivity)
      gcongr
    _ ≤ _ := by
      have hp : 0 ≤ (N : ℝ)^2 * baseWeight N beta^2 := by positivity
      nlinarith

theorem quadratic_moment_small {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    (hsmall : (q : ℝ) ≤ sourceP N / 1000) {beta : ℝ}
    (hb : 1/2 ≤ beta ∧ beta ≤ 1) :
    0.4939 * (N : ℝ)^2 * baseWeight N beta^2 ≤
      (finiteMoment N (deltaRadius N q) 1 beta beta).re := by
  have hm := (realMass_bounds (nat_pos_of_exp_le hN) (r := 1)
    (s := beta) (t := beta) le_rfl hb.2 hb.2).1
  have he := (Complex.re_le_norm
    (fullMoment N 1 beta beta - finiteMoment N (deltaRadius N q) 1 beta beta)).trans
      (quadratic_tail_small hN hq hsmall hb)
  have hf := fullMoment_real (nat_pos_of_exp_le hN) 1 beta beta
  simp only [Complex.ofReal_one] at hf
  rw [hf, Complex.sub_re, Complex.ofReal_re] at he
  have hw : baseWeight N 1 = 1 := by simp [baseWeight]
  simp only [hw, one_mul] at hm
  have hp : 0 ≤ (N : ℝ)^2 * baseWeight N beta^2 := by positivity
  nlinarith

theorem actual_exceptional_quadratic_credit {N p : ℕ} [NeZero p]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hp : p.Prime) (hn : ¬ p ∣ N)
    (hsmall : (p : ℝ) ≤ sourceP N / 1000)
    {chi : Character p} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (heven : chi (-1) = 1) :
    (1.4817 * (p : ℝ) / (p.totient : ℝ)^3) * (N : ℝ)^2 * baseWeight N rho.re^2 ≤
      (quadraticCoefficient N chi *
        finiteMoment N (deltaRadius N p) 1 rho.re rho.re).re := by
  have hq : (p : ℝ) ≤ sourceP N := by linarith [sourceP_pos hN]
  have hc := exceptionalValues_quadratic_simple hN hq hr
  have hbeta := mem_zeroValues.mp (Finset.mem_filter.mp hr).1
  rw [quadraticCoefficient_prime_even hp hn chi hc.1 hc.2.1 heven]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hm := quadratic_moment_small hN hp.pos hsmall
    ⟨hbeta.2.2.2.2, hbeta.2.2.1.le⟩
  have he := mul_le_mul_of_nonneg_left hm
    (by positivity : 0 ≤ 3 * (p : ℝ) / (p.totient : ℝ)^3)
  convert he using 1
  · rfl
  · ring

def primeQuadraticPayment {p : ℕ} [NeZero p] (N : ℕ)
    (chi : Character p) (rho : ℂ) : ℝ :=
  paidLower N (deltaRadius N p) rho.re 0
      (linearCoefficient N chi) 0 (cubicCoefficient N chi) +
    (1.4817 * (p : ℝ) / (p.totient : ℝ)^3) * (N : ℝ)^2 * baseWeight N rho.re^2

theorem primeQuadraticPayment_le {N p : ℕ} [NeZero p]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hp : p.Prime) (hn : ¬ p ∣ N)
    (hsmall : (p : ℝ) ≤ sourceP N / 1000)
    {chi : Character p} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (heven : chi (-1) = 1) :
    primeQuadraticPayment N chi rho ≤ (exceptionalArc N p).re := by
  have hq : (p : ℝ) ≤ sourceP N := by linarith [sourceP_pos hN]
  have hb := (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
  have hbase := jointFinite_re_lower (nat_pos_of_exp_le hN) hb
    (deltaRadius_pos hN hp.pos) 0 (linearCoefficient N chi) 0 (cubicCoefficient N chi)
  have he : exceptionalArc N p =
      jointFinite N (deltaRadius N p) rho.re 0 (linearCoefficient N chi) 0
        (cubicCoefficient N chi) +
      quadraticCoefficient N chi * finiteMoment N (deltaRadius N p) 1 rho.re rho.re := by
    rw [exceptionalArc_eq_joint hN hq hr]
    unfold jointFinite
    ring
  rw [he, Complex.add_re]
  exact add_le_add hbase (actual_exceptional_quadratic_credit hN hp hn hsmall hr heven)

theorem exceptionalIntegral_single_upgrade {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : q ∈ denominators (sourceP N))
    {L : ℝ} (hL : L ≤ (exceptionalArc N q).re) :
    totalExceptionalPayment N +
      (L - localExceptionalPayment N q) ≤ (exceptionalIntegral N).re := by
  have he : (exceptionalIntegral N).re =
      ∑ r ∈ denominators (sourceP N), (exceptionalArc N r).re := by
    rw [exceptionalIntegral, coreIndices, Finset.sum_sigma, Complex.re_sum]
    rfl
  rw [he, totalExceptionalPayment,
    ← Finset.sum_erase_add _ _ hq, ← Finset.sum_erase_add _ _ hq]
  have hrest :
      (∑ r ∈ (denominators (sourceP N)).erase q, localExceptionalPayment N r) ≤
        ∑ r ∈ (denominators (sourceP N)).erase q, (exceptionalArc N r).re := by
    apply Finset.sum_le_sum
    intro r hr
    have hh := (mem_denominators (sourceP_pos hN).le r).mp (Finset.mem_erase.mp hr).2
    let : NeZero r := ⟨by omega⟩
    exact exceptionalArc_re_lower hN hh.2
  linarith

theorem lambdaTripleCount_with_prime_quadratic_credit {N p : ℕ} [NeZero p]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hp : p.Prime) (hn : ¬ p ∣ N)
    (hsmall : (p : ℝ) ≤ sourceP N / 1000)
    {chi : Character p} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (heven : chi (-1) = 1) :
    0.48166084 * (N : ℝ)^2 + totalExceptionalPayment N +
      (max (localExceptionalPayment N p) (primeQuadraticPayment N chi rho) -
        localExceptionalPayment N p) +
      (regularInteractionIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hq : (p : ℝ) ≤ sourceP N := by linarith [sourceP_pos hN']
  have hmem := (mem_denominators (sourceP_pos hN').le p).mpr ⟨hp.one_le, hq⟩
  have hL := max_le (exceptionalArc_re_lower hN' hq)
    (primeQuadraticPayment_le hN' hp hn hsmall hr heven)
  have he := exceptionalIntegral_single_upgrade hN' hmem hL
  linarith [lambdaTripleCount_ge_exceptional_regular hN hodd]

end LiuWang.Proof.MajorZeroMomentPayment
