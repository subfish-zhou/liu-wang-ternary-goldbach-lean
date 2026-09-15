import LiuWang.Proof.SingularSeries.LowerBound

/-!
# Acceptance surfaces for the proved part of the singular-series task

There is no theorem here claiming the numerical endpoint (4.8).
The infinite-series, local-factor, positivity, cutoff, and actual
finite-radius integral surfaces are kept distinct.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped Interval
open AnalyticNumberTheory.LargeSieve LiuWang.Proof.Interfaces
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.SingularSeries

theorem source_absolute_convergence {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    Summable (fun q : ℕ => ‖coefficient N q‖) :=
  coefficient_norm_summable (nat_pos_of_exp_le hN)

theorem source_euler_identity {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∑' q : ℕ, coefficient N q) =
      ((∏' p : Nat.Primes,
        (if (p : ℕ) ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2
         else 1 + 1 / ((p : ℝ) - 1) ^ 3) : ℝ) : ℂ) :=
  original_series_eq_eulerProduct (nat_pos_of_exp_le hN)

theorem source_positive_lower_bound {N : ℕ} (hN : Odd N) :
    0 < 2 * universalProduct ∧
      2 * universalProduct ≤ (∑' q : ℕ, coefficient N q).re := by
  rw [← ofReal_series, Complex.ofReal_re]
  exact ⟨mul_pos (by norm_num) universalProduct_pos, two_mul_universalProduct_le_series hN⟩

theorem source_radius_integral_truncation {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : 0 < q) :
    ‖(N : ℂ) ^ 2 * ((0.997 : ℂ) ^ 2 / 2) -
      (∫ eta in -deltaRadius N q..deltaRadius N q,
        J N eta ^ 3 * charReal (-(N : ℝ) * eta))‖ ≤
      1 / (Real.pi ^ 3 * deltaRadius N q ^ 2) :=
  cube_integral_truncation (nat_pos_of_exp_le hN)
    (deltaRadius_pos (exp_2000_le_of_exp_3100_le hN) hq)

example (N : ℕ) : coefficient N 0 = 0 := coefficient_zero N

example (N : ℕ) : coefficient N 1 = 1 := coefficient_one N

example {N : ℕ} (hN : Odd N) : localFactor N 2 = 2 := localFactor_two_of_odd hN

example {P : ℝ} (hP : 0 ≤ P) (q : ℕ) :
    q ∈ denominators P ↔ 1 ≤ q ∧ (q : ℝ) ≤ P := mem_denominators hP q

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    I11 N = (fullMass N : ℂ) * (series N : ℂ) -
      (fullMass N : ℂ) * coefficientTail N (sourceP N) - arcError N :=
  I11_eq_series_main_sub_errors hN

end LiuWang.Proof.SingularSeries
