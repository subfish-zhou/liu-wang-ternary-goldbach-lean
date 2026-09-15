import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.TotientPower

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget

theorem endpoint_scale_le {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1) :
    0 ≤ 1.02*baseWeight N beta ∧ 1.02*baseWeight N beta ≤ 1.02 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw := Real.rpow_le_one_of_one_le_of_nonpos hn (sub_nonpos.mpr hb)
  constructor
  · unfold baseWeight; positivity
  · unfold baseWeight
    linarith

theorem sharpConductorCost_large {N r : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (hr : 1600000000 ≤ r) :
    sharpConductorCost N r beta ≤ 0.25*(N : ℝ)^2 := by
  have hrR : (1600000000 : ℝ) ≤ r := by exact_mod_cast hr
  have hφ : 0 < (r.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have hs0 := Real.sqrt_nonneg (r : ℝ)
  have hs : (Real.sqrt (r : ℝ))^2 = (r : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsL : (40000 : ℝ) ≤ Real.sqrt r := by nlinarith
  have hz := endpoint_scale_le hN hb
  have hp : conductorPolynomial r (1.02*baseWeight N beta) ≤
      1.062*(r : ℝ)*Real.sqrt r := by
    apply (conductorPolynomial_mono r hz.1 hz.2).trans
    unfold conductorPolynomial
    norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) hs0,
      mul_nonneg (sub_nonneg.mpr hsL) (Nat.cast_nonneg r)]
  have ht := totient_large_sqrt_ratio (r := r) (a := 200) (by norm_num)
    (by norm_num; exact hr)
  have hc : 6.69*conductorPolynomial r (1.02*baseWeight N beta) ≤
      0.25*(r.totient : ℝ)^2 := by nlinarith
  rw [sharpConductorCost, div_le_iff₀ (sq_pos_of_pos hφ)]
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ))]

theorem quadraticSourceCost_large {N r : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (hr : 10000 ≤ r) :
    quadraticSourceCost N r beta ≤ 0.15*(N : ℝ)^2 := by
  have hrR : (10000 : ℝ) ≤ r := by exact_mod_cast hr
  have hφ : 0 < (r.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have hs0 := Real.sqrt_nonneg (r : ℝ)
  have hs : (Real.sqrt (r : ℝ))^2 = (r : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsL : (100 : ℝ) ≤ Real.sqrt r := by nlinarith
  have ht := totient_large_sqrt_ratio (r := r) (a := 10) (by norm_num)
    (by norm_num; exact hr)
  have hc : 1000*(r : ℝ) ≤ 7*(r.totient : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsL) (Nat.cast_nonneg r)]
  have hz := endpoint_scale_le hN hb
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hzmul := mul_le_mul_of_nonneg_left hz2 (by positivity : 0 ≤ 20.07*(r : ℝ))
  have he : 20.07*(r : ℝ)*(1.02*baseWeight N beta)^2 ≤
      0.15*(r.totient : ℝ)^2 := by nlinarith
  rw [quadraticSourceCost, div_le_iff₀ (sq_pos_of_pos hφ)]
  nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg (N : ℝ))]

theorem sourceCost_large {N r : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (hr : 1600000000 ≤ r) :
    sourceCost N r beta ≤ 0.25*(N : ℝ)^2 :=
  (sourceCost_le_sharp N r beta).trans (sharpConductorCost_large hN hb hr)

theorem sourceCost_non_coprime_large {N r : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (hr : 10000 ≤ r) (hnc : ¬ Nat.Coprime N r) :
    sourceCost N r beta ≤ 0.15*(N : ℝ)^2 := by
  rw [sourceCost, if_neg hnc]
  exact quadraticSourceCost_large hN hb hr

theorem sourceP_large_conductor_regression {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (29791000000 : ℝ) ≤ sourceP N ∧
      Finset.Icc 1600000000 ⌊sourceP N⌋₊ ≠ ∅ := by
  have hL := sourceL_ge_3100 hN
  have hP : (29791000000 : ℝ) ≤ sourceP N := by
    unfold sourceP
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3]
  refine ⟨hP, Finset.nonempty_iff_ne_empty.mp ?_⟩
  refine ⟨1600000000, Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩
  apply (Nat.le_floor_iff (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le).mpr
  norm_num
  linarith

theorem exceptional_large_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi)
    (hr : 1600000000 ≤ chi.conductor) :
    max (max (totalAllModuliExceptionalPayment N) (-sourceCost N chi.conductor rho.re))
        (-0.25*(N : ℝ)^2) ≤ (exceptionalIntegral N).re := by
  have hb := (mem_zeroValues.mp (Finset.mem_filter.mp hrho).1).2.2.1.le
  have hc := sourceCost_large (nat_pos_of_exp_le hN) hb hr
  have hp := exceptionalIntegral_paid_source hN hq hrho
  apply max_le hp
  exact (by linarith : -0.25*(N : ℝ)^2 ≤ -sourceCost N chi.conductor rho.re).trans
    ((le_max_right _ _).trans hp)

theorem exceptional_non_coprime_large_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi)
    (hr : 10000 ≤ chi.conductor) (hnc : ¬ Nat.Coprime N chi.conductor) :
    max (max (totalAllModuliExceptionalPayment N) (-sourceCost N chi.conductor rho.re))
        (-0.15*(N : ℝ)^2) ≤ (exceptionalIntegral N).re := by
  have hb := (mem_zeroValues.mp (Finset.mem_filter.mp hrho).1).2.2.1.le
  have hc := sourceCost_non_coprime_large (nat_pos_of_exp_le hN) hb hr hnc
  have hp := exceptionalIntegral_paid_source hN hq hrho
  apply max_le hp
  exact (by linarith : -0.15*(N : ℝ)^2 ≤ -sourceCost N chi.conductor rho.re).trans
    ((le_max_right _ _).trans hp)

theorem lambdaTripleCount_large_conductor {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi)
    (hr : 1600000000 ≤ chi.conductor) :
    0.23166084*(N : ℝ)^2 + totalEnhancedRegularPayment N + (regularHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have he := (le_max_right _ _).trans (exceptional_large_paid hN' hq hrho hr)
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split hN', Complex.add_re] at h
  linarith [enhancedPayment_integral hN']

theorem lambdaTripleCount_non_coprime_conductor {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi)
    (hr : 10000 ≤ chi.conductor) (hnc : ¬ Nat.Coprime N chi.conductor) :
    0.33166084*(N : ℝ)^2 + totalEnhancedRegularPayment N + (regularHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have he := (le_max_right _ _).trans (exceptional_non_coprime_large_paid hN' hq hrho hr hnc)
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split hN', Complex.add_re] at h
  linarith [enhancedPayment_integral hN']

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget
