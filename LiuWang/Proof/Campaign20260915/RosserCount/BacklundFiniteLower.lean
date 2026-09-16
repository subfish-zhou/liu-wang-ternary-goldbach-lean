import LiuWang.Proof.Campaign20260915.RosserCount.BacklundEulerLower

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_finite_dirichlet_lower {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    (∑ n ∈ range N, (n + 1 : ℝ) ^ (-σ)) ≤ ‖riemannZeta (σ : ℂ)‖ := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have hsum := (summable_nat_add_iff
    (f := fun n : ℕ => 1 / (n : ℂ) ^ (σ : ℂ)) 1).mpr
      (Complex.summable_one_div_nat_cpow.mpr hs)
  have he (n : ℕ) : (1 / ((n + 1 : ℕ) : ℂ) ^ (σ : ℂ)).re =
      (n + 1 : ℝ) ^ (-σ) := by
    rw [← ofReal_natCast, ← ofReal_cpow (Nat.cast_nonneg (n + 1)),
      ← ofReal_one, ← ofReal_div, ofReal_re, one_div,
      ← Real.rpow_neg (Nat.cast_nonneg (n + 1))]
    push_cast
    rfl
  have hr := hasSum_re hsum.hasSum
  have hl := Summable.sum_le_tsum (range N)
    (fun n _ => show 0 ≤ (1 / ((n + 1 : ℕ) : ℂ) ^ (σ : ℂ)).re by rw [he]; positivity)
    hr.summable
  rw [hr.tsum_eq] at hl
  simp only [he] at hl
  simp only [Nat.cast_add, Nat.cast_one] at hl
  rw [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at hl
  exact hl.trans (re_le_norm _)

theorem backlund_five_halves_term_lower {x u : ℝ}
    (hx : 0 < x) (hu : 0 < u) (hsq : x ≤ u ^ 2) :
    1 / (x ^ 2 * u) ≤ x ^ (-5 / 2 : ℝ) := by
  have hs : Real.sqrt x ≤ u := (Real.sqrt_le_iff).mpr ⟨hu.le, hsq⟩
  have he : x ^ (-5 / 2 : ℝ) = 1 / (x ^ 2 * Real.sqrt x) := by
    rw [show (-5 / 2 : ℝ) = -(2 + 1 / 2) by norm_num,
      Real.rpow_neg hx.le, Real.rpow_add hx, Real.rpow_ofNat,
      ← Real.sqrt_eq_rpow, one_div]
  rw [he]
  exact one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_left hs (sq_nonneg x))

#print axioms backlund_finite_dirichlet_lower
#print axioms backlund_five_halves_term_lower

end LiuWang.Proof.Campaign20260915.RosserCount
