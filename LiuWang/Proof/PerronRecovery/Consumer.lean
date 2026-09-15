import LiuWang.Proof.PerronRecovery.Oscillation

/-! Concrete sums on the original closed domains. These are recovered
consumers, not claims about the principal character, full R12 or Goldbach. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace LiuWang.Proof.PerronRecovery

open Interfaces Parameters FixedHeightZeroSum

theorem primitive_nonprincipal_psi_sum {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 3 ≤ q)
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) +
        ∑ p ∈ highZeroIndices chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
          (t : ℂ) ^ completedZeroValue p / completedZeroValue p‖ ≤
      0.961615 * t / (Real.log (N : ℝ)) ^ (15 : ℕ) *
        (Real.log (N : ℝ)) ^ (2 : ℕ) :=
  primitive_psi_le hN hq hqUpper hchi hPrimitive htlo hthi

theorem nonprincipal_psi_sum {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {t : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) +
        ∑ p ∈ highZeroIndices chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
          (t : ℂ) ^ completedZeroValue p / completedZeroValue p‖ ≤
      0.961616 * t / (Real.log (N : ℝ)) ^ (15 : ℕ) *
        (Real.log (N : ℝ)) ^ (2 : ℕ) :=
  nonprincipal_psi_le chi hN hqUpper hchi htlo hthi

theorem nonprincipal_psi_sum_multiplicity {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {t : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) +
        ∑ rho ∈ NonprincipalPsi.highZeroValues chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * ((t : ℂ) ^ rho / rho)‖ ≤
      0.961616 * t / (Real.log (N : ℝ)) ^ (15 : ℕ) *
        (Real.log (N : ℝ)) ^ (2 : ℕ) := by
  rw [NonprincipalPsi.sum_highZeroValues_multiplicity hchi]
  exact nonprincipal_psi_sum hN hqUpper hchi htlo hthi

theorem nonprincipal_closed_window {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : Character q} (hchi : chi ≠ 1) (eta : ℝ) :
    ‖(∑ n ∈ windowFinset N, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n *
        AnalyticNumberTheory.LargeSieve.charReal (eta * n)) +
      ∑ p ∈ highZeroIndices chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
        Jrho N (completedZeroValue p) eta‖ ≤
      (0.96258 + 3.02102 * (N : ℝ) * |eta|) * (N : ℝ) /
        (Real.log (N : ℝ)) ^ (15 : ℕ) * (Real.log (N : ℝ)) ^ (2 : ℕ) :=
  nonprincipal_oscillation_le chi hN hqUpper hchi eta

theorem nonprincipal_twistedS {N q : ℕ} [NeZero q]
    (chi : Character q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1) (eta : ℝ) :
    ‖CharacterExpansion.twistedS N eta chi +
      ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) eta‖ ≤
      (0.96258 + 3.02102 * (N : ℝ) * |eta|) * (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  rw [← NonprincipalExpansion.S_chi_eq_twistedS]
  exact nonprincipal_oscillation_le chi hN hqUpper hchi eta

end LiuWang.Proof.PerronRecovery
