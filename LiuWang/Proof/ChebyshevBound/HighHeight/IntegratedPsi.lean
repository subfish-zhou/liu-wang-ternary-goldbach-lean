import LiuWang.Proof.ChebyshevBound.HighHeight.SmoothedZeroSum
import LiuWang.Proof.ChebyshevBound.Mass

/-! # 实际 Λ 的线性平滑有限和及无条件去平滑方向。 -/

set_option autoImplicit false
noncomputable section

open Finset

namespace LiuWang.Proof.ChebyshevBound.HighHeight

def integratedPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (x - n)

theorem integratedPsi_difference_ge {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (y - x) * Chebyshev.psi x ≤ integratedPsi y - integratedPsi x := by
  have hy : 0 ≤ y := hx.trans hxy
  have hsub : Ioc 0 ⌊x⌋₊ ⊆ Ioc 0 ⌊y⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_le_floor hxy)
  have hsum :
      (∑ n ∈ Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (y - n)) ≤
        integratedPsi y := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro n hn _
    have hnle : (n : ℝ) ≤ y :=
      (by exact_mod_cast (mem_Ioc.mp hn).2 : (n : ℝ) ≤ ⌊y⌋₊).trans (Nat.floor_le hy)
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr hnle)
  have heq : (y - x) * Chebyshev.psi x + integratedPsi x =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (y - n) := by
    simp only [Chebyshev.psi, integratedPsi, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    ring
  linarith

theorem psi_le_integrated_difference {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    Chebyshev.psi x ≤ (integratedPsi (x + h) - integratedPsi x) / h := by
  apply (le_div_iff₀ hh).2
  simpa [mul_comm] using integratedPsi_difference_ge hx (show x ≤ x + h by linarith)

theorem sum_mangoldt_le_integrated_difference (N : ℕ) {h : ℝ} (hh : 0 < h) :
    (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n) ≤
      (integratedPsi ((N : ℝ) + h) - integratedPsi (N : ℝ)) / h := by
  rw [sum_mangoldt_Icc_eq_psi]
  exact psi_le_integrated_difference (Nat.cast_nonneg N) hh

theorem archimedean_psi_correction_nonpos {t : ℝ} (ht : 2 ≤ t) :
    -Real.log (2 * Real.pi) - Real.log (1 - t⁻¹ ^ 2) / 2 ≤ 0 := by
  have hi : 0 ≤ t⁻¹ := inv_nonneg.mpr (by linarith)
  have hi2 : t⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) ht
  have harg : 1 / 2 ≤ 1 - t⁻¹ ^ 2 := by nlinarith
  have hlog : -Real.log 2 ≤ Real.log (1 - t⁻¹ ^ 2) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) harg
    simpa using h
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
  linarith [log_two_ge_two_thirds, log_pi_ge_one]

end LiuWang.Proof.ChebyshevBound.HighHeight
