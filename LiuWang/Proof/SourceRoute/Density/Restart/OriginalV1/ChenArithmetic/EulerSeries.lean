import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

theorem moebius_div_sq_summable :
    Summable (fun n : ℕ => (μ n : ℝ) / (n : ℝ) ^ 2) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    hasSum_zeta_two.summable
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))) (sq_nonneg _)

theorem moebius_div_sq_tsum :
    (∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2) = 6 / Real.pi ^ 2 := by
  have h := LSeries_one_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_one_eq_riemannZeta (by norm_num), riemannZeta_two] at h
  have he : LSeries (fun n => (μ n : ℂ)) 2 =
      ((∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2) : ℂ) := by
    simp only [LSeries, Complex.ofReal_intCast, Complex.ofReal_natCast]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n; simp [LSeries.term]
    · simp [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat]
  rw [he] at h
  have hr : (Real.pi ^ 2 / 6) * (∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2) = 1 := by
    exact_mod_cast h
  apply (eq_div_iff (pow_ne_zero 2 Real.pi_ne_zero)).mpr
  linarith

theorem reciprocal_sq_tail {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, 1 / ((n + N : ℕ) : ℝ) ^ 2) ≤
      1 / (N : ℝ) ^ 2 + 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ha : AntitoneOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ici (N : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : (-2 : ℝ) ≤ 0)).mono
      (Ici_subset_Ioi.mpr hNr)
  have ht := ha.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hNr)
    (fun t ht => Real.rpow_nonneg (hNr.le.trans ht.le) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hNr] at ht
  have hs := (summable_nat_add_iff N).mpr hasSum_zeta_two.summable
  rw [hs.tsum_eq_zero_add]
  simp only [zero_add]
  have he (n : ℕ) : ((n : ℝ) ^ (-2 : ℝ)) = 1 / (n : ℝ) ^ 2 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two, one_div]
  simp only [he] at ht
  norm_num [Real.rpow_neg hNr.le, Real.rpow_neg_one] at ht
  convert add_le_add_right ht (1 / (N : ℝ) ^ 2) using 1 <;>
    simp [add_comm, add_assoc]

theorem moebius_div_sq_tail {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ range N, (μ n : ℝ) / (n : ℝ) ^ 2) - 6 / Real.pi ^ 2| ≤
      1 / (N : ℝ) ^ 2 + 1 / (N : ℝ) := by
  rw [← moebius_div_sq_tsum, ← moebius_div_sq_summable.sum_add_tsum_nat_add N,
    sub_add_cancel_left, abs_neg]
  have hs := (summable_nat_add_iff N).mpr moebius_div_sq_summable
  have hp := (summable_nat_add_iff N).mpr hasSum_zeta_two.summable
  have hn : |∑' n : ℕ, (μ (n + N) : ℝ) / ((n + N : ℕ) : ℝ) ^ 2| ≤
      ∑' n : ℕ, ‖(μ (n + N) : ℝ) / ((n + N : ℕ) : ℝ) ^ 2‖ := by
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  exact hn.trans
    ((hs.norm.tsum_le_tsum (fun n => by
      rw [Real.norm_eq_abs, abs_div, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ ((n + N : ℕ) : ℝ) from Nat.cast_nonneg _)]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n + N)))
        (sq_nonneg _)) hp).trans (reciprocal_sq_tail hN))

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic
