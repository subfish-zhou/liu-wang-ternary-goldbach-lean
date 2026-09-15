import LiuWang.Proof.ParameterComparisons.Main

/-! Scalar preparations for the source's far-arc estimate. No exponential-sum
bound is assumed or asserted. -/
set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.ParameterComparisons

/-- Endpoint control after multiplying `a/t + b*t` by its positive variable.
This is the scalar justification for the source's maximum of two endpoints. -/
theorem inverse_linear_le_of_endpoints {a b C l t u : ℝ}
    (hb : 0 ≤ b) (hl : 0 < l) (hlt : l ≤ t) (htu : t ≤ u)
    (hleft : a / l + b * l ≤ C) (hright : a / u + b * u ≤ C) :
    a / t + b * t ≤ C := by
  have ht : 0 < t := hl.trans_le hlt
  have hu : 0 < u := ht.trans_le htu
  rcases eq_or_lt_of_le (hlt.trans htu) with heq | hlu
  · have het : t = l := le_antisymm (by simpa [heq] using htu) hlt
    simpa [het] using hleft
  · have hL : 0 ≤ C * l - a - b * l ^ 2 := by
      have h := (div_le_iff₀ hl).mp (show a / l ≤ C - b * l by linarith)
      nlinarith
    have hU : 0 ≤ C * u - a - b * u ^ 2 := by
      have h := (div_le_iff₀ hu).mp (show a / u ≤ C - b * u by linarith)
      nlinarith
    have h1 := mul_nonneg (sub_nonneg.mpr htu) hL
    have h2 := mul_nonneg (sub_nonneg.mpr hlt) hU
    have h3 := mul_nonneg (sub_nonneg.mpr hlu.le)
      (mul_nonneg hb (mul_nonneg (sub_nonneg.mpr hlt) (sub_nonneg.mpr htu)))
    have hprod : 0 ≤ (u - l) * (C * t - a - b * t ^ 2) := by
      nlinarith
    have hmid := nonneg_of_mul_nonneg_right hprod (sub_pos.mpr hlu)
    have hdiv : a / t ≤ C - b * t := by
      apply (div_le_iff₀ ht).mpr
      nlinarith
    linarith

/-- A full-domain fifth-root scale bound from the quadratic exponential estimate. -/
theorem thousand_mul_cube_lt_exp_fifth {x : ℝ} (hx : 2000 ≤ x) :
    1000 * x ^ (3 : ℕ) < Real.exp (x / 5) := by
  have hx0 : 0 ≤ x := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg (x := x / 20) (by positivity)
  have hsmall : x < Real.exp (x / 20) := by
    nlinarith [mul_nonneg hx0 (show 0 ≤ x - 2000 by linarith)]
  have hp := pow_lt_pow_left₀ hsmall hx0 (n := 4) (by norm_num)
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  rw [show (4 : ℝ) * (x / 20) = x / 5 by ring] at hp
  have hx3 : 0 ≤ x ^ (3 : ℕ) := pow_nonneg hx0 _
  calc
    1000 * x ^ (3 : ℕ) ≤ x * x ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right (by linarith) hx3
    _ = x ^ (4 : ℕ) := by ring
    _ < Real.exp (x / 5) := hp

end LiuWang.Proof.ParameterComparisons
