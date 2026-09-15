import LiuWang.Proof.NearOneDensity.Continuation.Frontier.JointCount

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearOneDensity.Continuation.Frontier

def improvedBound (r : DensityRow) : ℕ := if r = .r0478 then 13000 else rowBound r

theorem improvedBound_le (r : DensityRow) : improvedBound r ≤ rowBound r := by
  by_cases hr : r = .r0478
  · subst r
    norm_num [improvedBound, rowBound, rowMultiplicity, rowSelectedBound]
  · simp [improvedBound, hr]

theorem improvedBound_last : improvedBound .r0478 = 13000 ∧
    improvedBound .r0478 < rowBound .r0478 := by
  norm_num [improvedBound, rowBound, rowMultiplicity, rowSelectedBound]

theorem improved_table_bound (r : DensityRow) {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ rowLambda r) :
    zeroCount q (1 - lam / Real.log z) y ≤ improvedBound r := by
  by_cases hr : r = .r0478
  · subst r
    exact joint_last_zeroCount hz hqy hlam hupper
  · rw [improvedBound, if_neg hr]
    exact effective_table_bound r hz hqy hlam hupper

theorem improved_familyCount (r : DensityRow) {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ rowLambda r) :
    DirichletZeroCount.familyCount q (1 - lam / Real.log z) y ≤ improvedBound r := by
  rw [familyCount_eq_zeroCount (source_alpha_ge_half hz (hupper.trans (row_basic_certificate r).2.1))]
  exact improved_table_bound r hz hqy hlam hupper

theorem improved_family_tail (r : DensityRow) {q : ℕ} [NeZero q] {z alpha y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - rowLambda r / Real.log z ≤ alpha) :
    DirichletZeroCount.familyCount q alpha y ≤ improvedBound r := by
  have hl : 0.262132 ≤ rowLambda r := by cases r <;> norm_num [rowLambda]
  exact (familyCount_antitone_alpha ha).trans (improved_familyCount r hz hqy hl le_rfl)

theorem improved_inverse_band (r : DensityRow) {q : ℕ} [NeZero q] {z alpha u y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - rowLambda r / Real.log z ≤ alpha) (hu : 0 < u) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ DirichletZeroCount.bandValues χ alpha u y,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) / |ρ.im|) ≤ (improvedBound r : ℝ) / u :=
  inverse_band_of_family_bound (improved_family_tail r hz hqy ha) hu

theorem improved_inverse_sqrt_band (r : DensityRow) {q : ℕ} [NeZero q] {z alpha u y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - rowLambda r / Real.log z ≤ alpha) (hu : 0 < u) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ DirichletZeroCount.bandValues χ alpha u y,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) / Real.sqrt |ρ.im|) ≤
        (improvedBound r : ℝ) / Real.sqrt u := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
    (fun χ _ => DirichletZeroCount.band_weighted_sum_le_count χ alpha u y
      (fun ρ => 1 / Real.sqrt |ρ.im|) (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt u)
      (fun _ hρ => one_div_le_one_div_of_le (Real.sqrt_pos.mpr hu)
        (Real.sqrt_le_sqrt (DirichletZeroCount.mem_bandValues.mp hρ).2.2.2)))
  simp only [mul_one_div, one_div_mul_eq_div, ← Finset.sum_div, ← Nat.cast_sum] at hh
  exact hh.trans (div_le_div_of_nonneg_right
    (by exact_mod_cast improved_family_tail r hz hqy ha) (Real.sqrt_nonneg _))

theorem improved_source_one_le_height (r : DensityRow) {q : ℕ} [NeZero q]
    {x y z lam : ℝ} (hqx : (q : ℝ) ≤ x) (hy : 1 ≤ y)
    (hz : 100000000000 ≤ z) (hxy : x * y ≤ z)
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ rowLambda r) :
    zeroCount q (1 - lam / Real.log z) y ≤ improvedBound r := by
  apply improved_table_bound r hz _ hlam hupper
  rw [max_eq_right hy]
  exact (mul_le_mul_of_nonneg_right hqx (by linarith)).trans hxy

theorem improved_source_level_le_z (r : DensityRow) {q : ℕ} [NeZero q]
    {x y z lam : ℝ} (hqx : (q : ℝ) ≤ x) (hqz : (q : ℝ) ≤ z)
    (hz : 100000000000 ≤ z) (hxy : x * y ≤ z)
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ rowLambda r) :
    zeroCount q (1 - lam / Real.log z) y ≤ improvedBound r := by
  by_cases hy : 1 ≤ y
  · exact improved_source_one_le_height r hqx hy hz hxy hlam hupper
  · apply improved_table_bound r hz _ hlam hupper
    simpa only [max_eq_left (le_of_not_ge hy), mul_one] using hqz

theorem improved_complete_count (r : DensityRow) {q : ℕ} [NeZero q] {z alpha y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - rowLambda r / Real.log z ≤ alpha) :
    (∑ χ : DirichletCharacter ℂ q,
      ∑ ρ ∈ (CompleteExpansion.zeroValues χ y).filter (fun ρ => alpha ≤ ρ.re),
        analyticOrderNatAt χ.LFunction ρ) ≤ improvedBound r := by
  have hhalf := (source_alpha_ge_half hz (row_basic_certificate r).2.1).trans ha
  rw [← DirichletZeroCount.Applications.familyCount_eq_complete_filter q hhalf]
  exact improved_family_tail r hz hqy ha

end LiuWang.Proof.NearOneDensity.Continuation.Frontier
