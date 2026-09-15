import LiuWang.Proof.MajorZeroInteraction.Exceptional

/-! Quantified arithmetic savings for the actual signed integrals.
These statements do not assert a numerical bound on the remaining zero moments. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.MajorZeroInteraction

theorem weight_nonneg {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    0 ≤ arithmeticWeight N chi :=
  (norm_nonneg _).trans (norm_phaseCoefficient_le_weight N chi)

theorem signedCost_nonneg (N q : ℕ) : 0 ≤ signedCost N q := by
  by_cases hq : q = 0
  · simp [signedCost, hq]
  · let : NeZero q := ⟨hq⟩
    rw [signedCost_eq]
    exact Finset.sum_nonneg fun chi _ => mul_nonneg (weight_nonneg N chi) (norm_nonneg _)

theorem signedCost_le_totient {q : ℕ} [NeZero q] (N : ℕ) :
    signedCost N q ≤
      (q.totient : ℝ) * ∑ chi : Character q, ‖signedArcCoefficient N chi‖ := by
  rw [signedCost_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun chi _ =>
    mul_le_mul_of_nonneg_right (arithmeticWeight_le_totient N chi) (norm_nonneg _)

theorem weight_prime_coprime {p : ℕ} [NeZero p] (hp : p.Prime)
    {N : ℕ} (hn : ¬ p ∣ N) (chi : Character p) :
    arithmeticWeight N chi ≤ Real.sqrt (p : ℝ) := by
  have hcop : Nat.Coprime N p := (hp.coprime_iff_not_dvd.mpr hn).symm
  by_cases hc : chi = 1
  · simp only [arithmeticWeight, hc, ramanujan_prime N hp, if_neg hn,
      norm_neg, norm_one]
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hp.one_le)
  · simp only [arithmeticWeight, if_neg hc, if_neg hn, if_pos hcop]
    apply (min_le_right _ _).trans
    apply Real.sqrt_le_sqrt
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi

theorem signedCost_prime_coprime {p : ℕ} [NeZero p] (hp : p.Prime)
    {N : ℕ} (hn : ¬ p ∣ N) :
    signedCost N p ≤
      Real.sqrt (p : ℝ) * ∑ chi : Character p, ‖signedArcCoefficient N chi‖ := by
  rw [signedCost_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun chi _ =>
    mul_le_mul_of_nonneg_right (weight_prime_coprime hp hn chi) (norm_nonneg _)

theorem prime_weight_strict_saving {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    Real.sqrt (p : ℝ) < (p.totient : ℝ) := by
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  apply (Real.sqrt_lt' (by linarith : (0 : ℝ) < p - 1)).mpr
  nlinarith [sq_nonneg ((p : ℝ) - 3)]

theorem norm_prime_arc_interaction {N p : ℕ} [NeZero p] (hN : 0 < N)
    (hp : p.Prime) (hn : ¬ p ∣ N) :
    ‖∑ a ∈ numerators p,
      ∫ eta in -deltaRadius N p..deltaRadius N p,
        interactionKernel N a p eta * arcPhase N a p eta‖ ≤
      Real.sqrt (p : ℝ) * ∑ chi : Character p, ‖signedArcCoefficient N chi‖ :=
  (norm_arc_interaction_le hN).trans (signedCost_prime_coprime hp hn)

theorem exceptionalIntegral_eq_zero_of_none {N : ℕ}
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    exceptionalIntegral N = 0 := by
  rw [exceptionalIntegral]
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨hq, ha⟩ := Finset.mem_sigma.mp hi
  let : NeZero i.1 := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  have he (eta : ℝ) : exceptionalKernel N i.2 i.1 eta = 0 :=
    (interaction_no_exceptional N i.2 eta (mem_numerators.mp ha).2.2
      (hnone i.1 hq)).1
  simp only [he, zero_mul, intervalIntegral.integral_zero]

theorem lambdaTripleCount_no_exceptional {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    0.48166084 * (N : ℝ)^2 + (regularInteractionIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ) * alpha)).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ lambdaTripleCount N := by
  simpa only [exceptionalIntegral_eq_zero_of_none hnone, Complex.zero_re, add_zero] using
    lambdaTripleCount_ge_exceptional_regular hN hodd

theorem lambdaTripleCount_ge_decimal_signedCost {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.481660839 * (N : ℝ)^2 - totalSignedCost N +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ) * alpha)).re ≤
        lambdaTripleCount N := by
  linarith [lambdaTripleCount_ge_signedCost hN hodd,
    log_power_le_decimal (exp_2000_le_of_exp_3100_le hN)]

end LiuWang.Proof.MajorZeroInteraction
