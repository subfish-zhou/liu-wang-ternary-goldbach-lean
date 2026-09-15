import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Ramified
import LiuWang.Proof.SingularSeries.Uniform.Abel

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier

theorem reciprocal_totient_multiples (X : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ Finset.Icc 1 X, if d ∣ q then 1/(q.totient : ℝ)^2 else 0) ≤
      44/(d.totient : ℝ)^2 := by
  rw [Uniform.sum_multiples _ X hd]
  have hφ : 0 < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 (X/d), (1/(d.totient : ℝ)^2) * (1/(k.totient : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : 0 < (k.totient : ℝ) :=
        Nat.cast_pos.mpr (Nat.totient_pos.mpr (Finset.mem_Icc.mp hk).1)
      have he : (d.totient : ℝ)*(k.totient : ℝ) ≤ ((d*k).totient : ℝ) := by
        exact_mod_cast Nat.totient_super_multiplicative d k
      have h := one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos hφ hk0))
        (pow_le_pow_left₀ (mul_nonneg hφ.le hk0.le) he 2)
      simpa only [mul_pow, one_div, mul_inv] using h
    _ = (1/(d.totient : ℝ)^2) *
        ∑ k ∈ Finset.Icc 1 (X/d), 1/(k.totient : ℝ)^2 := (Finset.mul_sum ..).symm
    _ ≤ (1/(d.totient : ℝ)^2) * 44 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using Uniform.inverse_totient_tail_finite (m := 1) (B := X/d) (by omega)
    _ = _ := by ring

theorem coefficient_norms_conductor {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    ‖linearCoefficient N chi‖ ≤ 3*Real.sqrt chi.conductor/(q.totient : ℝ)^2 ∧
    ‖quadraticCoefficient N chi‖ ≤ 3*(chi.conductor : ℝ)/(q.totient : ℝ)^2 ∧
    ‖cubicCoefficient N chi‖ ≤
      (chi.conductor : ℝ)*Real.sqrt chi.conductor/(q.totient : ℝ)^2 := by
  have hφ : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hm : ‖principalCoefficient q‖ ≤ 1/(q.totient : ℝ) := by
    rw [principalCoefficient, norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (norm_moebius_complex_le q) hφ.le
  have hg : ‖gaussScale chi‖ ≤ Real.sqrt chi.conductor/(q.totient : ℝ) := by
    simpa only [DirichletCharacter.conductor_inv, div_eq_mul_inv, mul_comm] using gaussScale_norm_le chi
  have hh := norm_phaseCoefficient_le_totient N chi
  have hR := norm_ramanujan_le_totient N q
  have hs : (Real.sqrt (chi.conductor : ℝ))^2 = (chi.conductor : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  constructor
  · rw [linearCoefficient, norm_mul, norm_mul, norm_mul, norm_pow]
    norm_num only [norm_neg, Complex.norm_ofNat]
    calc
      _ ≤ 3*(1/(q.totient : ℝ))^2 *
          (Real.sqrt chi.conductor/(q.totient : ℝ)) * (q.totient : ℝ) := by gcongr
      _ = _ := by field_simp
  constructor
  · rw [quadraticCoefficient, norm_mul, norm_mul, norm_mul, norm_pow]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ 3*(1/(q.totient : ℝ)) *
          (Real.sqrt chi.conductor/(q.totient : ℝ))^2 * (q.totient : ℝ) := by gcongr
      _ = _ := by rw [div_pow, hs]; field_simp
  · rw [cubicCoefficient, norm_mul, norm_neg, norm_pow]
    calc
      _ ≤ (Real.sqrt chi.conductor/(q.totient : ℝ))^3 * (q.totient : ℝ) := by gcongr
      _ = _ := by rw [div_pow, pow_succ _ 2, hs]; field_simp

def conductorPolynomial (d : ℕ) (u : ℝ) : ℝ :=
  3*Real.sqrt d*u + 3*(d : ℝ)*u^2 + (d : ℝ)*Real.sqrt d*u^3

theorem conductorPolynomial_nonneg (d : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ conductorPolynomial d u := by unfold conductorPolynomial; positivity

theorem exceptionalArc_norm_conductor {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ‖exceptionalArc N q‖ ≤
      (3/Real.pi) * (N : ℝ)^2 * conductorPolynomial chi.conductor (realEndpoint N rho.re) /
        (q.totient : ℝ)^2 := by
  have hn := nat_pos_of_exp_le hN
  have hb := (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
  have hd := (deltaRadius_pos hN (NeZero.pos q)).le
  have h1 := finite_real_triple_uniform hn le_rfl le_rfl hb hd
  have h2 := finite_real_triple_uniform hn le_rfl hb hb hd
  have h3 := finite_real_triple_uniform hn hb hb hb hd
  have he : realEndpoint N 1 = 1 := by simp [realEndpoint]
  simp only [he, one_mul, Complex.ofReal_one] at h1 h2
  rw [exceptionalArc_eq_joint hN hq hr, jointFinite]
  simp only [zero_mul, zero_add]
  have hc := coefficient_norms_conductor N chi
  have hh := (norm_add_le
    (linearCoefficient N chi * finiteMoment N (deltaRadius N q) 1 1 rho.re +
      quadraticCoefficient N chi * finiteMoment N (deltaRadius N q) 1 rho.re rho.re)
    (cubicCoefficient N chi * finiteMoment N (deltaRadius N q) rho.re rho.re rho.re)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  simp only [norm_mul] at hh
  apply hh.trans
  have hu : 0 ≤ realEndpoint N rho.re := by unfold realEndpoint; positivity
  calc
    _ ≤ (3*Real.sqrt chi.conductor/(q.totient : ℝ)^2) *
        ((3/Real.pi)*(N : ℝ)^2*realEndpoint N rho.re) +
      (3*(chi.conductor : ℝ)/(q.totient : ℝ)^2) *
        ((3/Real.pi)*(N : ℝ)^2*(realEndpoint N rho.re*realEndpoint N rho.re)) +
      ((chi.conductor : ℝ)*Real.sqrt chi.conductor/(q.totient : ℝ)^2) *
        ((3/Real.pi)*(N : ℝ)^2*
          (realEndpoint N rho.re*realEndpoint N rho.re*realEndpoint N rho.re)) := by
      exact add_le_add
        (add_le_add (mul_le_mul hc.1 h1 (norm_nonneg _) (by positivity))
          (mul_le_mul hc.2.1 h2 (norm_nonneg _) (by positivity)))
        (mul_le_mul hc.2.2 h3 (norm_nonneg _) (by positivity))
    _ = _ := by unfold conductorPolynomial; ring

theorem fixed_source_absolute_total {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      (∑ s ∈ denominators (sourceP N), ‖exceptionalArc N s‖) ≤
        (132/Real.pi) * (N : ℝ)^2 *
          conductorPolynomial d.modulus (realEndpoint N rho.re) / (d.modulus.totient : ℝ)^2 := by
  obtain ⟨d, _, hdc, _, _, hall⟩ := exceptionalValues_same_source hN hq hr
  refine ⟨d, hdc, ?_⟩
  have hd : 0 < d.modulus := by rw [hdc]; exact Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hu : 0 ≤ realEndpoint N rho.re := by unfold realEndpoint; positivity
  let K := (3/Real.pi)*(N : ℝ)^2*conductorPolynomial d.modulus (realEndpoint N rho.re)
  have hK : 0 ≤ K := mul_nonneg (by positivity) (conductorPolynomial_nonneg _ hu)
  have hlocal (s : ℕ) (hs : s ∈ denominators (sourceP N)) :
      ‖exceptionalArc N s‖ ≤ K * (if d.modulus ∣ s then 1/(s.totient : ℝ)^2 else 0) := by
    have hs' := (mem_denominators (sourceP_pos hN).le s).mp hs
    let : NeZero s := ⟨by omega⟩
    by_cases hex : ∃ (psi : Character s) (tau : ℂ), tau ∈ exceptionalValues N psi
    · obtain ⟨psi, tau, ht⟩ := hex
      have hsrc := hall s hs'.2 psi tau ht
      have hb := exceptionalArc_norm_conductor hN hs'.2 ht
      rw [hsrc.1, ← hsrc.2.1] at hb
      rw [if_pos hsrc.2.2.1]
      exact hb.trans_eq (by dsimp [K]; ring)
    · have hn : ∀ psi : Character s, exceptionalValues N psi = ∅ := by
        intro psi
        exact Finset.eq_empty_iff_forall_notMem.mpr (fun tau ht => hex ⟨psi, tau, ht⟩)
      rw [(exceptionalArc_no_exception N hn).1, norm_zero]
      split_ifs <;> positivity
  apply (Finset.sum_le_sum hlocal).trans
  rw [← Finset.mul_sum]
  have hm := reciprocal_totient_multiples ⌊sourceP N⌋₊ hd
  exact (mul_le_mul_of_nonneg_left hm hK).trans_eq (by dsimp [K]; ring)

def totalConductorCost (N d : ℕ) (beta : ℝ) : ℝ :=
  (132/Real.pi)*(N : ℝ)^2 *
    conductorPolynomial d (realEndpoint N beta)/(d.totient : ℝ)^2

theorem exceptionalIntegral_paid_conductor {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      -totalConductorCost N d.modulus rho.re ≤ (exceptionalIntegral N).re := by
  obtain ⟨d, hd, hb⟩ := fixed_source_absolute_total hN hq hr
  refine ⟨d, hd, ?_⟩
  have he : exceptionalIntegral N = ∑ s ∈ denominators (sourceP N), exceptionalArc N s := by
    rw [exceptionalIntegral, coreIndices, Finset.sum_sigma]
    rfl
  have hn : ‖exceptionalIntegral N‖ ≤ totalConductorCost N d.modulus rho.re := by
    rw [he]
    exact (norm_sum_le _ _).trans hb
  have h := Complex.re_le_norm (-exceptionalIntegral N)
  rw [Complex.neg_re, norm_neg] at h
  linarith

theorem lambdaTripleCount_conductor_direct {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      0.48166084*(N : ℝ)^2 +
        max (totalAllModuliExceptionalPayment N) (-totalConductorCost N d.modulus rho.re) +
        totalEnhancedRegularPayment N + (regularHigherIntegral N).re +
        (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
        (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
        6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  obtain ⟨d, hd, hb⟩ := exceptionalIntegral_paid_conductor hN' hq hr
  refine ⟨d, hd, ?_⟩
  have hm := max_le (exceptionalIntegral_allModuli_payment hN') hb
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split hN', Complex.add_re] at h
  linarith [enhancedPayment_integral hN']

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier
