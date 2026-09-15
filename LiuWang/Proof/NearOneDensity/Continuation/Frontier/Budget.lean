import LiuWang.Proof.NearOneDensity.TableCertificates

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.NearOneDensity.Continuation.Frontier

def savedMass (a c x : ℝ) : ℝ := 1 / a - c * x

theorem saved_strict_interval {a ell k c H x : ℝ} {K : ℕ}
    (hx : 0 ≤ x) (hxH : x ≤ H)
    (hp₂ : 0 ≤ (K + 1 : ℝ) * 0.0755 ^ 2 - c ^ 2 + K * c * 0.7647)
    (hderiv : -2 * (K + 1 : ℝ) * (1 / (a + ell) - k) * 0.0755 +
      2 * (1 / a) * c - K * ((1 / a) * 0.7647 - c * k) +
      2 * ((K + 1 : ℝ) * 0.0755 ^ 2 - c ^ 2 + K * c * 0.7647) * H ≤ 0)
    (hend : savedMass a c H ^ 2 + K * savedMass a c H * crossBudget k H <
      (K + 1 : ℝ) * zeroBudget a ell k H ^ 2) :
    savedMass a c x ^ 2 + K * savedMass a c x * crossBudget k x <
      (K + 1 : ℝ) * zeroBudget a ell k x ^ 2 := by
  have h := quadratic_decreasing_on_interval (p₀ := 0) hx hxH hp₂ hderiv
  dsimp [savedMass, crossBudget, zeroBudget] at hend ⊢
  nlinarith

theorem saved_continuous_budget {a ell c H lam x k : ℝ} {K : ℕ}
    (ha : 0 < a + lam) (hlam : lam ≤ ell)
    (hc : 0 ≤ c) (hx : 0 ≤ x) (hxH : x ≤ H) (hk : k ≤ 0.2763932023)
    (hAend : 0 ≤ savedMass a c H)
    (hBAend : crossBudget 0.2763932023 H ≤ savedMass a c H)
    (hDend : 0 ≤ zeroBudget a ell 0.2763932023 H)
    (hp₂ : 0 ≤ (K + 1 : ℝ) * 0.0755 ^ 2 - c ^ 2 + K * c * 0.7647)
    (hderiv : -2 * (K + 1 : ℝ) * (1 / (a + ell) - 0.2763932023) * 0.0755 +
      2 * (1 / a) * c - K * ((1 / a) * 0.7647 - c * 0.2763932023) +
      2 * ((K + 1 : ℝ) * 0.0755 ^ 2 - c ^ 2 + K * c * 0.7647) * H ≤ 0)
    (hend : savedMass a c H ^ 2 + K * savedMass a c H * crossBudget 0.2763932023 H <
      (K + 1 : ℝ) * zeroBudget a ell 0.2763932023 H ^ 2) :
    0 ≤ savedMass a c x ∧ crossBudget k x ≤ savedMass a c x ∧
    0 ≤ zeroBudget a lam k x ∧
    0 < zeroBudget a lam k x ^ 2 - savedMass a c x * crossBudget k x ∧
    (savedMass a c x ^ 2 - savedMass a c x * crossBudget k x) /
      (zeroBudget a lam k x ^ 2 - savedMass a c x * crossBudget k x) < K + 1 := by
  have hmass : savedMass a c H ≤ savedMass a c x := by
    unfold savedMass
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hxH)]
  have hcross : crossBudget k x ≤ crossBudget 0.2763932023 H := by
    unfold crossBudget
    linarith
  have hrec := one_div_le_one_div_of_le ha (show a + lam ≤ a + ell by linarith)
  have hD : zeroBudget a ell 0.2763932023 H ≤ zeroBudget a ell 0.2763932023 x := by
    unfold zeroBudget
    linarith
  have hDlam : zeroBudget a ell 0.2763932023 x ≤ zeroBudget a lam k x := by
    unfold zeroBudget
    linarith
  have hA := hAend.trans hmass
  have hBA := hcross.trans (hBAend.trans hmass)
  have hD0 := hDend.trans hD
  have hbudget := saved_strict_interval hx hxH hp₂ hderiv hend
  have hB : crossBudget k x ≤ crossBudget 0.2763932023 x := by
    unfold crossBudget
    linarith
  have hpaid : savedMass a c x ^ 2 + K * savedMass a c x * crossBudget k x <
      (K + 1 : ℝ) * zeroBudget a lam k x ^ 2 := by
    have hleft := mul_le_mul_of_nonneg_left hB (mul_nonneg (Nat.cast_nonneg K) hA)
    have hsq : zeroBudget a ell 0.2763932023 x ^ 2 ≤ zeroBudget a lam k x ^ 2 := by
      nlinarith
    have hright := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ K + 1 by positivity)
    linarith
  exact ⟨hA, hBA, hD0.trans hDlam, ratio_lt_of_strict_budget hA hBA hpaid⟩

theorem strong_last_budget {lam x k : ℝ}
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ 0.478)
    (hx : 0 ≤ x) (hxH : x ≤ 1 / 25.328436) (hk : k ≤ 0.2763932023) :
    0 ≤ savedMass 0.311 (719 / 800) x ∧
    crossBudget k x ≤ savedMass 0.311 (719 / 800) x ∧
    0 ≤ zeroBudget 0.311 lam k x ∧
    0 < zeroBudget 0.311 lam k x ^ 2 - savedMass 0.311 (719 / 800) x * crossBudget k x ∧
    (savedMass 0.311 (719 / 800) x ^ 2 - savedMass 0.311 (719 / 800) x * crossBudget k x) /
      (zeroBudget 0.311 lam k x ^ 2 - savedMass 0.311 (719 / 800) x * crossBudget k x) < 6900 + 1 := by
  exact saved_continuous_budget (K := 6900) (by linarith) hupper (by norm_num)
    hx hxH hk (by norm_num [savedMass]) (by norm_num [savedMass, crossBudget])
    (by norm_num [zeroBudget]) (by norm_num) (by norm_num)
    (by norm_num [savedMass, crossBudget, zeroBudget])

end LiuWang.Proof.NearOneDensity.Continuation.Frontier
