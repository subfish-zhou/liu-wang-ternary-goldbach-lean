import LiuWang.Proof.SourceRoute.ThirdArc.Heights
import LiuWang.Proof.PrimePowerRemoval.Main

/-! The prime-only sum and the Lambda sum have an actual prime-power difference. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.PrimePowerRemoval

namespace LiuWang.Proof.SourceRoute.ThirdArc

def primeS (N : ℕ) (alpha : ℝ) : ℂ :=
  ∑ n ∈ windowFinset N, (primeLogWeight n : ℂ) * charReal ((n : ℝ) * alpha)

theorem lambda_sub_prime_identity (N : ℕ) (alpha : ℝ) :
    S N alpha - primeS N alpha =
      ∑ n ∈ windowFinset N, (primePowerWeight n : ℂ) * charReal ((n : ℝ) * alpha) := by
  rw [CompleteExpansion.S_eq_closed_sum, primeS, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [primePowerWeight, Complex.ofReal_sub, sub_mul]

theorem norm_lambda_sub_prime_le_mass (N : ℕ) (alpha : ℝ) :
    ‖S N alpha - primeS N alpha‖ ≤ ∑ n ∈ windowFinset N, primePowerWeight n := by
  rw [lambda_sub_prime_identity]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro n _
  rw [norm_mul, VaughanTypeI.norm_charReal_eq_one, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (primePowerWeight_nonneg n)]

theorem norm_lambda_sub_prime_le {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (alpha : ℝ) :
    ‖S N alpha - primeS N alpha‖ ≤ Real.sqrt N * sourceL N :=
  (norm_lambda_sub_prime_le_mass N alpha).trans (primePowerMass_le_sqrt_mul_log hN)

theorem primeS_three_bands {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    ‖primeS N (rationalCenter a q + eta)‖ ≤
      CompleteExpansion.principalMass q * (0.999 * (N : ℝ)) +
        CompleteExpansion.errorBound q N a eta +
        (sigma4 N q + sigma5 N q + sigma6 N q) + Real.sqrt N * sourceL N := by
  calc
    _ = ‖S N (rationalCenter a q + eta) -
        (S N (rationalCenter a q + eta) - primeS N (rationalCenter a q + eta))‖ := by
      congr 1
      ring
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add
      (S_three_bands (exp_2000_le_of_exp_3100_le hN) hi hq heta)
      (norm_lambda_sub_prime_le hN _))

end LiuWang.Proof.SourceRoute.ThirdArc
