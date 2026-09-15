import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
# 实际 Λ 有限和及平方和

ψ 保留全部素数幂。平方和结论保留 ψ(N)，不假设或暗示尖锐总量界。
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LiuWang.Proof.ChebyshevBound

theorem sum_mangoldt_Icc_eq_psi (N : ℕ) :
    (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n) = Chebyshev.psi (N : ℝ) := by
  simp [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc]

theorem sum_mangoldt_sq_le_log_mul_psi (N : ℕ) :
    (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2) ≤
      Real.log N * Chebyshev.psi (N : ℝ) := by
  rw [← sum_mangoldt_Icc_eq_psi, mul_sum]
  apply sum_le_sum
  intro n hn
  have hn' := mem_Icc.mp hn
  have hlog : ArithmeticFunction.vonMangoldt n ≤ Real.log N :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn'.1) (by exact_mod_cast hn'.2))
  simpa only [pow_two] using
    mul_le_mul_of_nonneg_right hlog
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))

theorem sum_mangoldt_sq_subset_le_log_mul_psi {N : ℕ} (s : Finset ℕ)
    (hs : s ⊆ Icc 1 N) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n ^ 2) ≤
      Real.log N * Chebyshev.psi (N : ℝ) :=
  (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)).trans
    (sum_mangoldt_sq_le_log_mul_psi N)

end LiuWang.Proof.ChebyshevBound
