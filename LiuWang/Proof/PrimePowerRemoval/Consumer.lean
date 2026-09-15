import LiuWang.Proof.PrimePowerRemoval.Main

set_option autoImplicit false

noncomputable section

open Finset ArithmeticFunction
open LiuWang.Proof.Interfaces LiuWang.Proof.PrimePowerRemoval
open scoped BigOperators

example (n : ℕ) :
    primePowerWeight n = if n.Prime then 0 else vonMangoldt n :=
  primePowerWeight_eq_nonprime n

example (n : ℕ) : 0 ≤ primePowerWeight n :=
  primePowerWeight_nonneg n

example (n : ℕ) :
    0 < primePowerWeight n ↔ IsPrimePow n ∧ ¬n.Prime :=
  primePowerWeight_pos_iff n

example (n : ℕ) :
    0 < primePowerWeight n ↔ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ^ k = n :=
  primePowerWeight_pos_iff_exists_prime_pow n

example {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ windowFinset N, primePowerWeight n) ≤
      Chebyshev.psi N - Chebyshev.theta N :=
  primePowerMass_le_psi_sub_theta hN

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∑ n ∈ windowFinset N, primePowerWeight n) ≤
      Real.sqrt N * sourceL N :=
  primePowerMass_le_sqrt_mul_log hN

example (N : ℕ) : 0 ≤ I N := I_nonneg N

example (N : ℕ) : I N ≤ lambdaTripleCount N :=
  I_le_lambdaTripleCount N

example (N : ℕ) :
    lambdaTripleCount N - I N =
      ∑ i ∈ windowFinset N, ∑ j ∈ windowFinset N, ∑ k ∈ windowFinset N,
        if i + j + k = N ∧ (¬i.Prime ∨ ¬j.Prime ∨ ¬k.Prime) then
          vonMangoldt i * vonMangoldt j * vonMangoldt k else 0 :=
  lambdaTripleCount_sub_I_eq_nonprime_triples N

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lambdaTripleCount N - I N ≤
      3 * (N : ℝ) ^ ((3 : ℝ) / 2) * sourceL N ^ (3 : ℕ) :=
  lambdaTripleCount_sub_I_le hN

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    0 ≤ lambdaTripleCount N - I N ∧
      lambdaTripleCount N -
        3 * (N : ℝ) ^ ((3 : ℝ) / 2) * sourceL N ^ (3 : ℕ) ≤ I N :=
  primePowerRemoval hN

example {N : ℕ} (hI : 0 < I N) :
    ∃ p ∈ windowFinset N, ∃ q ∈ windowFinset N, ∃ r ∈ windowFinset N,
      p.Prime ∧ q.Prime ∧ r.Prime ∧ N = p + q + r :=
  exists_window_primes_of_I_pos hI

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (hI : 0 < I N) :
    LiuWang.IsThreeOddPrimeSum N :=
  isThreeOddPrimeSum_of_I_pos hN hI

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lambdaTripleCount N - I N < (3 / 1000 : ℝ) * (N : ℝ) ^ (2 : ℕ) :=
  lambdaTripleCount_sub_I_lt_budget hN

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hLambda : (0.5437 - 0.51 : ℝ) * (N : ℝ) ^ (2 : ℕ) ≤ lambdaTripleCount N) :
    (0.03 : ℝ) * (N : ℝ) ^ (2 : ℕ) ≤ I N :=
  I_lower_bound_of_lambda_lower_bound hN hLambda

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hLambda : (0.5437 - 0.51 : ℝ) * (N : ℝ) ^ (2 : ℕ) ≤ lambdaTripleCount N) :
    LiuWang.IsThreeOddPrimeSum N :=
  isThreeOddPrimeSum_of_lambda_lower_bound hN hLambda

example : (3 : ℕ) ∈ windowFinset 3000 := by
  norm_num [mem_windowFinset_iff, mem_windowSet_iff]

example : (3 : ℕ) ∉ windowFinset 3001 := by
  norm_num [mem_windowFinset_iff, mem_windowSet_iff]

example : (4 : ℕ) ∈ windowFinset 3001 := by
  norm_num [mem_windowFinset_iff, mem_windowSet_iff]

example : (3001 : ℕ) ∈ windowFinset 3001 := by
  norm_num [mem_windowFinset_iff, mem_windowSet_iff]

example : 0 < primePowerWeight 4 :=
  (primePowerWeight_pos_iff_exists_prime_pow 4).2 ⟨2, 2, by norm_num, by norm_num, rfl⟩

example : primePowerWeight 6 = 0 := by
  have hnot : ¬IsPrimePow 6 := by decide
  rw [primePowerWeight_eq_nonprime]
  norm_num [vonMangoldt_eq_zero_iff.mpr hnot]

example : LiuWang.IsThreeOddPrimeSum 9 := by
  exact ⟨3, 3, 3, by norm_num, by norm_num, by norm_num,
    by decide, by decide, by decide, rfl⟩
