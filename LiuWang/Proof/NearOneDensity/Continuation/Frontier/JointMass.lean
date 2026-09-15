import LiuWang.Proof.NearOneDensity.Continuation.Frontier.Strong

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity.Continuation.Frontier

theorem row_functional_weight_mass (r : DensityRow) {z : ℝ} (hz : 100000000000 ≤ z) :
    let σ := 1 + rowA r / Real.log z
    (∑' n, dampedWeight σ (stechkinSigma σ) stechkinK n) ≤
      Real.log z * savedMass (rowA r)
        (stechkinK / (stechkinSigma σ - 1) + 159 / 800) (1 / Real.log z) := by
  dsimp only
  rw [damped_mass_eq_zetaDamped (row_sigma_bounds r hz).1]
  have hσ := row_sigma_bounds r hz
  have hh := zeta_real_function hσ.1 (by linarith [hσ.2])
  have hL : Real.log z ≠ 0 := by linarith [source_log_lower hz]
  have ha := (row_basic_certificate r).1.ne'
  have he : 1 / (1 + rowA r / Real.log z - 1) -
      stechkinK / (stechkinSigma (1 + rowA r / Real.log z) - 1) - 159 / 800 =
      Real.log z * savedMass (rowA r)
        (stechkinK / (stechkinSigma (1 + rowA r / Real.log z) - 1) + 159 / 800)
        (1 / Real.log z) := by
    unfold savedMass
    field_simp [ha, hL]
    ring
  exact hh.trans_eq he

theorem last_joint_saving {z : ℝ} (hz : 100000000000 ≤ z) :
    0.908 ≤ stechkinK / (stechkinSigma (1 + rowA .r0478 / Real.log z) - 1) + 159 / 800 := by
  have hL : 25 ≤ Real.log z := by linarith [source_log_lower hz]
  have hσ := (row_sigma_bounds .r0478 hz).1
  have hσ₁ : 1 + rowA .r0478 / Real.log z ≤ 1013 / 1000 := by
    have hd : rowA .r0478 / Real.log z ≤ 13 / 1000 := by
      apply (div_le_iff₀ (by linarith)).mpr
      norm_num [rowA]
      linarith
    linarith
  have hτ : stechkinSigma (1 + rowA .r0478 / Real.log z) ≤ 163 / 100 := by
    have he := stechkinSigma_equation (1 + rowA .r0478 / Real.log z)
    have hg := stechkinSigma_ge hσ
    have hsquare : (1 + rowA .r0478 / Real.log z) ^ 2 ≤ (1013 / 1000 : ℝ) ^ 2 := by
      nlinarith
    nlinarith
  have hden : 0 < stechkinSigma (1 + rowA .r0478 / Real.log z) - 1 := by
    linarith [stechkinSigma_ge hσ]
  have hquot : (2837 / 4000 : ℝ) ≤
      stechkinK / (stechkinSigma (1 + rowA .r0478 / Real.log z) - 1) :=
    (le_div_iff₀ hden).mpr (by linarith [stechkinK_ge_447])
  linarith

theorem joint_last_weight_mass {z : ℝ} (hz : 100000000000 ≤ z) :
    let σ := 1 + rowA .r0478 / Real.log z
    (∑' n, dampedWeight σ (stechkinSigma σ) stechkinK n) ≤
      Real.log z * savedMass (rowA .r0478) 0.908 (1 / Real.log z) := by
  apply (row_functional_weight_mass .r0478 hz).trans
  have hL : 0 ≤ Real.log z := by linarith [source_log_lower hz]
  apply mul_le_mul_of_nonneg_left _ hL
  unfold savedMass
  exact sub_le_sub_left
    (mul_le_mul_of_nonneg_right (last_joint_saving hz) (source_inverse_log_bounds hz).1) _

theorem joint_last_budget {lam x k : ℝ}
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ 0.478)
    (hx : 0 ≤ x) (hxH : x ≤ 1 / 25.328436) (hk : k ≤ 0.2763932023) :
    0 ≤ savedMass 0.311 0.908 x ∧ crossBudget k x ≤ savedMass 0.311 0.908 x ∧
    0 ≤ zeroBudget 0.311 lam k x ∧
    0 < zeroBudget 0.311 lam k x ^ 2 - savedMass 0.311 0.908 x * crossBudget k x ∧
    (savedMass 0.311 0.908 x ^ 2 - savedMass 0.311 0.908 x * crossBudget k x) /
      (zeroBudget 0.311 lam k x ^ 2 - savedMass 0.311 0.908 x * crossBudget k x) < 6500 + 1 := by
  exact saved_continuous_budget (K := 6500) (by linarith) hupper (by norm_num)
    hx hxH hk (by norm_num [savedMass]) (by norm_num [savedMass, crossBudget])
    (by norm_num [zeroBudget]) (by norm_num) (by norm_num)
    (by norm_num [savedMass, crossBudget, zeroBudget])

end LiuWang.Proof.NearOneDensity.Continuation.Frontier
