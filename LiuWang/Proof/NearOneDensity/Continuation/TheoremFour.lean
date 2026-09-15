import LiuWang.Proof.NearOneDensity.Continuation.InducingCosts

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity.Continuation

theorem effective_table_bound (r : DensityRow) {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hlam₁ : lam ≤ rowLambda r) :
    zeroCount q (1 - lam / Real.log z) y ≤ rowBound r := by
  have hlam0 : 0 ≤ lam := by linarith
  have hL : 0 < Real.log z := by linarith [source_log_lower hz]
  have hα := source_alpha_ge_half hz (hlam₁.trans (row_basic_certificate r).2.1)
  obtain ⟨s, hsub, hcard, hsep⟩ := actual_paid_cluster_selection r hz hqy hlam0 hlam₁
  have hbudget := row_source_budget r hz hlam hlam₁
  change 0 ≤ massBudget (rowA r) (1 / Real.log z) ∧
    crossBudget stechkinConductorCoeff (1 / Real.log z) ≤ massBudget (rowA r) (1 / Real.log z) ∧
    0 ≤ zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z) ∧
    0 < zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z) ^ 2 -
      massBudget (rowA r) (1 / Real.log z) * crossBudget stechkinConductorCoeff (1 / Real.log z) ∧
    (massBudget (rowA r) (1 / Real.log z) ^ 2 -
      massBudget (rowA r) (1 / Real.log z) * crossBudget stechkinConductorCoeff (1 / Real.log z)) /
      (zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z) ^ 2 -
      massBudget (rowA r) (1 / Real.log z) * crossBudget stechkinConductorCoeff (1 / Real.log z)) <
        rowSelectedBound r + 1 at hbudget
  let σ := 1 + rowA r / Real.log z
  let A := Real.log z * massBudget (rowA r) (1 / Real.log z)
  let B := Real.log z * crossBudget stechkinConductorCoeff (1 / Real.log z)
  let D := Real.log z * zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z)
  have hσ := (row_sigma_bounds r hz).1
  have hgap : 0 < D ^ 2 - A * B := by
    have he : D ^ 2 - A * B = (Real.log z) ^ 2 *
        (zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z) ^ 2 -
          massBudget (rowA r) (1 / Real.log z) * crossBudget stechkinConductorCoeff (1 / Real.log z)) := by
      dsimp [A, B, D]
      ring
    rw [he]
    exact mul_pos (sq_pos_of_pos hL) hbudget.2.2.2.1
  have hcount := mixed_count s (fun p : ZeroIndex q => p.1.conductor)
    (fun p => p.1.primitiveCharacter) (fun p => p.2.1.im)
    hσ (hσ.trans_le (stechkinSigma_ge hσ)) (stechkinSigma_ge hσ) stechkinK_mem.2
    (mul_nonneg hL.le hbudget.1) (mul_le_mul_of_nonneg_left hbudget.2.1 hL.le)
    (mul_nonneg hL.le hbudget.2.2.1) (row_weight_mass_bound r hz)
    (fun p hp => by
      have hm := (mem_zeroFamily hα p).mp (hsub hp)
      exact inducing_row_selected_cost r p.1 hz hqy hlam0 hlam₁ hm.1 hm.2.1 hm.2.2.1 hm.2.2.2)
    (fun p hp u hu hpu => by
      have hm := (mem_zeroFamily hα p).mp (hsub hp)
      have hn := (mem_zeroFamily hα u).mp (hsub hu)
      exact inducing_row_cross_cost r p.1 u.1 hz hqy hm.2.2.2 hn.2.2.2
        (fun heq => (hsep p hp u hu hpu heq).le)) hgap
  have hrat : (A ^ 2 - A * B) / (D ^ 2 - A * B) < rowSelectedBound r + 1 := by
    dsimp [A, B, D]
    rw [scaled_ratio_eq hL.ne']
    exact hbudget.2.2.2.2
  have hs : s.card < rowSelectedBound r + 1 := by
    exact_mod_cast hcount.trans_lt hrat
  exact hcard.trans (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp hs))

theorem source_table_bound_of_one_le_height (r : DensityRow) {q : ℕ} [NeZero q]
    {x y z lam : ℝ} (hqx : (q : ℝ) ≤ x) (hy : 1 ≤ y)
    (hz : 100000000000 ≤ z) (hxy : x * y ≤ z)
    (hlam : 0.262132 ≤ lam) (hlam₁ : lam ≤ rowLambda r) :
    zeroCount q (1 - lam / Real.log z) y ≤ rowBound r := by
  apply effective_table_bound r hz _ hlam hlam₁
  rw [max_eq_right hy]
  exact (mul_le_mul_of_nonneg_right hqx (by linarith)).trans hxy

theorem source_table_bound_of_level_le_z (r : DensityRow) {q : ℕ} [NeZero q]
    {x y z lam : ℝ} (hqx : (q : ℝ) ≤ x) (hqz : (q : ℝ) ≤ z)
    (hz : 100000000000 ≤ z) (hxy : x * y ≤ z)
    (hlam : 0.262132 ≤ lam) (hlam₁ : lam ≤ rowLambda r) :
    zeroCount q (1 - lam / Real.log z) y ≤ rowBound r := by
  by_cases hy : 1 ≤ y
  · exact source_table_bound_of_one_le_height r hqx hy hz hxy hlam hlam₁
  · apply effective_table_bound r hz _ hlam hlam₁
    simpa only [max_eq_left (le_of_not_ge hy), mul_one] using hqz

theorem effective_multiplicity_sum_bound (r : DensityRow) {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hlam₁ : lam ≤ rowLambda r) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ zeroValues χ (1 - lam / Real.log z) y,
      analyticOrderNatAt χ.LFunction ρ) ≤ rowBound r := by
  rw [← zeroCount_eq_multiplicity_sum]
  exact effective_table_bound r hz hqy hlam hlam₁

end LiuWang.Proof.NearOneDensity.Continuation
