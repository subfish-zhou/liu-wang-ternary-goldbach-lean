import LiuWang.Proof.NearOneDensity.EulerBudget

set_option autoImplicit false
noncomputable section

open Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity

theorem quotientCharacter_ne_one {q : ℕ} [NeZero q]
    {χ ψ : DirichletCharacter ℂ q} (hχψ : χ ≠ ψ) : quotientCharacter χ ψ ≠ 1 := by
  change χ * star ψ ≠ 1
  rw [MulChar.star_eq_inv]
  exact fun h => hχψ (_root_.mul_inv_eq_one.mp h)

theorem height_difference_log {q : ℕ} [NeZero q] {y z t u : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ht : |t| ≤ y) (hu : |u| ≤ y) :
    Real.log q + Real.log (max 1 |t - u|) ≤ Real.log z + Real.log 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hm : max 1 |t - u| ≤ 2 * max 1 y := by
    apply max_le
    · linarith [le_max_left (1 : ℝ) y]
    · linarith [abs_sub t u, le_max_right (1 : ℝ) y]
  have hb := mul_le_mul_of_nonneg_left hm hq.le
  have hb' : (q : ℝ) * max 1 |t - u| ≤ z * 2 := by nlinarith
  have hm0 : 0 < max 1 |t - u| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hz0 : 0 < z := by linarith
  have hh := Real.log_le_log (mul_pos hq hm0) hb'
  rwa [Real.log_mul hq.ne' hm0.ne', Real.log_mul hz0.ne' (by norm_num)] at hh

theorem actual_distinct_character_cross_cost (r : DensityRow) {q : ℕ} [NeZero q]
    {y z lam : ℝ} (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam₁ : lam ≤ rowLambda r) (p s : ZeroIndex q)
    (hp : p ∈ zeroFamily q (1 - lam / Real.log z) y)
    (hs : s ∈ zeroFamily q (1 - lam / Real.log z) y) (hχ : p.1 ≠ s.1) :
    let σ := 1 + rowA r / Real.log z
    logKernel σ (stechkinSigma σ) stechkinK (quotientCharacter p.1 s.1)
      (p.2.1.im - s.2.1.im) ≤
        Real.log z * crossBudget stechkinConductorCoeff (1 / Real.log z) := by
  have hα := source_alpha_ge_half hz (hlam₁.trans (row_basic_certificate r).2.1)
  exact nonprincipal_row_cross_cost r _ (quotientCharacter_ne_one hχ) hz
    (height_difference_log hz hqy ((mem_zeroFamily hα p).mp hp).2.2.2
      ((mem_zeroFamily hα s).mp hs).2.2.2)

theorem actual_paid_cluster_selection (r : DensityRow) {q : ℕ} [NeZero q]
    {y z lam : ℝ} (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0 ≤ lam) (hlam₁ : lam ≤ rowLambda r) :
    ∃ u ⊆ zeroFamily q (1 - lam / Real.log z) y,
      zeroCount q (1 - lam / Real.log z) y ≤ rowMultiplicity r * u.card ∧
      ∀ p ∈ u, ∀ s ∈ u, p ≠ s → p.1 = s.1 →
        2 * (rowRadius r / Real.log z) < |p.2.1.im - s.2.1.im| := by
  have hL : 0 < Real.log z := by linarith [source_log_lower hz]
  exact actual_zero_cluster_selection _ _ (div_nonneg (rowRadius_nonneg r) hL.le)
    (rowMultiplicity r) (fun χ t =>
      source_row_window_count_effective_height r χ hz hqy hlam hlam₁ t)

end LiuWang.Proof.NearOneDensity
