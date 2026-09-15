import LiuWang.Proof.NearOneDensity.ClusteredCount
import LiuWang.Proof.NearOneDensity.TableCertificates
import LiuWang.Proof.NearOneDensity.Mass

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearOneDensity

def rowRadius : DensityRow → ℝ
  | .r027 | .r028 | .r030 => 0.7019
  | .r031 => 0.6897 | .r032 => 0.677 | .r033 => 0.6633
  | .r036 => 0.6219 | .r039 => 0.577 | .r042 => 0.5276
  | .r045 | .r046 | .r047 | .r0475 | .r0478 => 1.9039

theorem rowRadius_nonneg (r : DensityRow) : 0 ≤ rowRadius r := by
  cases r <;> norm_num [rowRadius]

theorem scaled_ratio_eq {A B D L : ℝ} (hL : L ≠ 0) :
    ((L * A) ^ 2 - (L * A) * (L * B)) /
      ((L * D) ^ 2 - (L * A) * (L * B)) =
      (A ^ 2 - A * B) / (D ^ 2 - A * B) := by
  have hnum : (L * A) ^ 2 - (L * A) * (L * B) = L ^ 2 * (A ^ 2 - A * B) := by ring
  have hden : (L * D) ^ 2 - (L * A) * (L * B) = L ^ 2 * (D ^ 2 - A * B) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero _ hL)]

/-- A literal all-character consumer, not an unconditional density theorem.
The three analytic costs and the closed-window occupancy remain explicit. -/
theorem source_table_bound_of_local_estimates (r : DensityRow)
    {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hlam : 0.262132 ≤ lam) (hupper : lam ≤ rowLambda r)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1)
    (hlocal : ∀ χ t, ((zeroFamily q (1 - lam / Real.log z) y).filter
      (fun p => p.1 = χ ∧ |p.2.1.im - t| ≤ rowRadius r / Real.log z)).card ≤ rowMultiplicity r)
    (hmass : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re -
        c * (-deriv riemannZeta (τ : ℂ) / riemannZeta (τ : ℂ)).re ≤
      Real.log z * massBudget (rowA r) (1 / Real.log z))
    (hzero : ∀ p ∈ zeroFamily q (1 - lam / Real.log z) y,
      logKernel σ τ c p.1 p.2.1.im ≤
        -(Real.log z * zeroBudget (rowA r) lam ((1 - 1 / Real.sqrt 5) / 2) (1 / Real.log z)))
    (hoff : ∀ p ∈ zeroFamily q (1 - lam / Real.log z) y,
      ∀ s ∈ zeroFamily q (1 - lam / Real.log z) y,
      p.1 ≠ s.1 ∨ 2 * (rowRadius r / Real.log z) < |p.2.1.im - s.2.1.im| →
      logKernel σ τ c (quotientCharacter p.1 s.1) (p.2.1.im - s.2.1.im) ≤
        Real.log z * crossBudget ((1 - 1 / Real.sqrt 5) / 2) (1 / Real.log z)) :
    zeroCount q (1 - lam / Real.log z) y ≤ rowBound r := by
  have hL : 0 < Real.log z := lt_of_lt_of_le (by norm_num) (source_log_lower hz)
  have h := row_source_budget r hz hlam hupper
  dsimp only at h
  have hmass' : (∑' n, dampedWeight σ τ c n) ≤
      Real.log z * massBudget (rowA r) (1 / Real.log z) := by
    rwa [damped_mass_eq_zeta hσ hτ]
  apply actual_zero_count_le_mul_of_clustered_logKernel (1 - lam / Real.log z) y
    (div_nonneg (rowRadius_nonneg r) hL.le) (rowMultiplicity r) (rowSelectedBound r)
    hlocal hσ hτ hστ hc (mul_nonneg hL.le h.1)
    (mul_le_mul_of_nonneg_left h.2.1 hL.le) (mul_nonneg hL.le h.2.2.1)
    hmass' hzero hoff
  · have heq : (Real.log z * zeroBudget (rowA r) lam ((1 - 1 / Real.sqrt 5) / 2)
        (1 / Real.log z)) ^ 2 -
        (Real.log z * massBudget (rowA r) (1 / Real.log z)) *
          (Real.log z * crossBudget ((1 - 1 / Real.sqrt 5) / 2) (1 / Real.log z)) =
      (Real.log z) ^ 2 * (zeroBudget (rowA r) lam ((1 - 1 / Real.sqrt 5) / 2)
        (1 / Real.log z) ^ 2 -
        massBudget (rowA r) (1 / Real.log z) *
          crossBudget ((1 - 1 / Real.sqrt 5) / 2) (1 / Real.log z)) := by ring
    rw [heq]
    exact mul_pos (sq_pos_of_pos hL) h.2.2.2.1
  · rw [scaled_ratio_eq hL.ne']
    exact h.2.2.2.2

end LiuWang.Proof.NearOneDensity
