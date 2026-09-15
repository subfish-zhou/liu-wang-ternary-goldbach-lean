import LiuWang.Proof.ChebyshevBound.Main
import LiuWang.Proof.ChebyshevBound.Mass

/-! # 已付前缀的实际消费者；所有未加权总量出口仍保留真实 ψ。 -/

set_option autoImplicit false

noncomputable section

open Finset
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.ChebyshevBound

theorem source_weighted_mangoldt_consumer {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n /
      (n : ℝ) ^ (1 + 1 / Real.log N)) ∧
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
      (n : ℝ) ^ (1 + 1 / Real.log N)) ≤ Real.log N + 8 :=
  ⟨summable_mangoldt_dirichlet (source_abscissa_mem hN).1,
    mangoldt_dirichlet_source_le hN⟩

theorem window_subset_mangoldt_prefix {N : ℕ} (hN : 0 < N) :
    windowFinset N ⊆ Icc 1 N := by
  intro n hn
  have hw := (mem_windowSet_iff N n).1 ((mem_windowFinset_iff N n).1 hn)
  exact mem_Icc.mpr ⟨by omega, hw.1⟩

theorem source_window_square_mass_consumer {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) ≤
      sourceL N * Chebyshev.psi (N : ℝ) :=
  sum_mangoldt_sq_subset_le_log_mul_psi (windowFinset N)
    (window_subset_mangoldt_prefix (nat_pos_of_exp_le hN))

theorem source_exponential_sum_consumer {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    ‖S N α‖ ≤ Chebyshev.psi (N : ℝ) := by
  have hmass :
      (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n) ≤
        Chebyshev.psi (N : ℝ) := by
    rw [← sum_mangoldt_Icc_eq_psi]
    exact sum_le_sum_of_subset_of_nonneg
      (window_subset_mangoldt_prefix (nat_pos_of_exp_le hN))
      (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  apply le_trans _ hmass
  change ‖∑ n ∈ windowFinset N,
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      AnalyticNumberTheory.LargeSieve.charReal ((n : ℝ) * α)‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  simp [AnalyticNumberTheory.LargeSieve.charReal, Complex.norm_exp,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

theorem low_height_zeta_consumer (t : ℝ) (ht : |t| ≤ 1 / 2) :
    riemannZeta ((3 / 4 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  apply riemannZeta_ne_zero_low_rectangle
  · norm_num
  · simpa using ht

end LiuWang.Proof.ChebyshevBound
