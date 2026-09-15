import LiuWang.Proof.NearOneDensity.Quadratic

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.NearOneDensity

def massBudget (a x : ℝ) : ℝ := 1 / a - 0.8973 * x
def crossBudget (k x : ℝ) : ℝ := k + 0.7647 * x
def zeroBudget (a lam k x : ℝ) : ℝ := 1 / (a + lam) - k - 0.0755 * x

theorem source_log_lower {z : ℝ} (hz : 100000000000 ≤ z) :
    25.328436 ≤ Real.log z := by
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h11 : Real.log (100000000000 : ℝ) = 11 * Real.log 10 := by
    rw [show (100000000000 : ℝ) = 10 ^ (11 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 100000000000) hz
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

theorem source_inverse_log_bounds {z : ℝ} (hz : 100000000000 ≤ z) :
    0 ≤ 1 / Real.log z ∧ 1 / Real.log z ≤ 1 / 25.328436 := by
  have h := source_log_lower hz
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) h⟩

theorem kappa_le_rational : (1 - 1 / Real.sqrt 5) / 2 ≤ (0.2763932023 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hu : Real.sqrt 5 ≤ 2.2360679776 := by nlinarith
  have hi : (0.4472135954 : ℝ) ≤ 1 / Real.sqrt 5 :=
    (le_div_iff₀ hp).mpr (by nlinarith)
  linarith

theorem quadratic_decreasing_on_interval {p₀ p₁ p₂ H x : ℝ}
    (_hx : 0 ≤ x) (hxH : x ≤ H) (hp₂ : 0 ≤ p₂) (hderiv : p₁ + 2 * p₂ * H ≤ 0) :
    p₀ + p₁ * H + p₂ * H ^ 2 ≤ p₀ + p₁ * x + p₂ * x ^ 2 := by
  have hs : p₁ + p₂ * (H + x) ≤ 0 := by
    nlinarith [mul_nonneg hp₂ (sub_nonneg.mpr hxH)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxH) (neg_nonneg.mpr hs)]

theorem strict_budget_on_interval {a ell k H x : ℝ} {K : ℕ}
    (hx : 0 ≤ x) (hxH : x ≤ H)
    (hp₂ : 0 ≤ (K + 1 : ℝ) * 0.0755 ^ 2 - 0.8973 ^ 2 + K * 0.8973 * 0.7647)
    (hderiv : -2 * (K + 1 : ℝ) * (1 / (a + ell) - k) * 0.0755 +
      2 * (1 / a) * 0.8973 - K * ((1 / a) * 0.7647 - 0.8973 * k) +
      2 * ((K + 1 : ℝ) * 0.0755 ^ 2 - 0.8973 ^ 2 + K * 0.8973 * 0.7647) * H ≤ 0)
    (hend : massBudget a H ^ 2 + K * massBudget a H * crossBudget k H <
      (K + 1 : ℝ) * zeroBudget a ell k H ^ 2) :
    massBudget a x ^ 2 + K * massBudget a x * crossBudget k x <
      (K + 1 : ℝ) * zeroBudget a ell k x ^ 2 := by
  have h := quadratic_decreasing_on_interval (p₀ := 0) hx hxH hp₂ hderiv
  dsimp [massBudget, crossBudget, zeroBudget] at hend ⊢
  nlinarith

theorem strict_budget_lambda_mono {a lam ell k x : ℝ} {K : ℕ}
    (ha : 0 < a + lam) (hlam : lam ≤ ell)
    (hD : 0 ≤ zeroBudget a ell k x)
    (hbudget : massBudget a x ^ 2 + K * massBudget a x * crossBudget k x <
      (K + 1 : ℝ) * zeroBudget a ell k x ^ 2) :
    massBudget a x ^ 2 + K * massBudget a x * crossBudget k x <
      (K + 1 : ℝ) * zeroBudget a lam k x ^ 2 := by
  have hrec := one_div_le_one_div_of_le ha (show a + lam ≤ a + ell by linarith)
  have hmono : zeroBudget a ell k x ≤ zeroBudget a lam k x := by
    unfold zeroBudget
    linarith
  have hsq : zeroBudget a ell k x ^ 2 ≤ zeroBudget a lam k x ^ 2 := by nlinarith
  exact hbudget.trans_le (mul_le_mul_of_nonneg_left hsq (by positivity))

theorem ratio_lt_of_strict_budget {A B D : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hBA : B ≤ A)
    (hbudget : A ^ 2 + K * A * B < (K + 1 : ℝ) * D ^ 2) :
    0 < D ^ 2 - A * B ∧ (A ^ 2 - A * B) / (D ^ 2 - A * B) < K + 1 := by
  have hn : 0 ≤ A ^ 2 - A * B := by nlinarith [mul_nonneg hA (sub_nonneg.mpr hBA)]
  have hgap : 0 < D ^ 2 - A * B := by
    by_contra! h
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (show (0 : ℝ) ≤ K + 1 by positivity) h
    nlinarith
  exact ⟨hgap, (div_lt_iff₀ hgap).mpr (by nlinarith)⟩

theorem table3_first_endpoint {x : ℝ} (hx : 0 ≤ x) (hxH : x ≤ 1 / 25.328) :
    massBudget 0.365 x ^ 2 + (7 : ℝ) * massBudget 0.365 x * crossBudget 0.276394 x <
      (8 : ℝ) * zeroBudget 0.365 0.27 0.276394 x ^ 2 := by
  have h := strict_budget_on_interval (a := 0.365) (ell := 0.27) (k := 0.276394)
    (K := 7) hx hxH (by norm_num) (by norm_num)
    (by norm_num [massBudget, crossBudget, zeroBudget])
  norm_num at h ⊢
  exact h

end LiuWang.Proof.NearOneDensity
