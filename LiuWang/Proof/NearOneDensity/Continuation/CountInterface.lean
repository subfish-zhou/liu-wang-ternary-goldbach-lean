import LiuWang.Proof.NearOneDensity.Continuation.TheoremFour
import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearOneDensity.Continuation

theorem count_values_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {alpha : ℝ} (ha : 1 / 2 ≤ alpha) (y : ℝ) :
    DirichletZeroCount.zeroValues χ alpha y = NearOneDensity.zeroValues χ alpha y := by
  ext ρ
  rw [DirichletZeroCount.mem_zeroValues, NearOneDensity.mem_zeroValues ha]
  constructor
  · rintro ⟨hz, ⟨_, hr, ht⟩, hα⟩
    exact ⟨hz, hα, hr, ht⟩
  · rintro ⟨hz, hα, hr, ht⟩
    exact ⟨hz, ⟨by linarith, hr, ht⟩, hα⟩

theorem familyCount_eq_zeroCount {q : ℕ} [NeZero q] {alpha y : ℝ} (ha : 1 / 2 ≤ alpha) :
    DirichletZeroCount.familyCount q alpha y = zeroCount q alpha y := by
  rw [zeroCount_eq_multiplicity_sum]
  simp only [DirichletZeroCount.familyCount, DirichletZeroCount.count, count_values_eq _ ha]

theorem effective_familyCount_bound (r : DensityRow) {q : ℕ} [NeZero q] {z lam y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hlam₁ : lam ≤ rowLambda r) :
    DirichletZeroCount.familyCount q (1 - lam / Real.log z) y ≤ rowBound r := by
  rw [familyCount_eq_zeroCount (source_alpha_ge_half hz (hlam₁.trans (row_basic_certificate r).2.1))]
  exact effective_table_bound r hz hqy hlam hlam₁

theorem familyCount_antitone_alpha {q : ℕ} [NeZero q] {a b y : ℝ} (hab : a ≤ b) :
    DirichletZeroCount.familyCount q b y ≤ DirichletZeroCount.familyCount q a y := by
  apply Finset.sum_le_sum
  intro χ _
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  obtain ⟨hz, hstrip, hb⟩ := DirichletZeroCount.mem_zeroValues.mp hρ
  exact DirichletZeroCount.mem_zeroValues.mpr ⟨hz, hstrip, hab.trans hb⟩

theorem familyCount_row_tail (r : DensityRow) {q : ℕ} [NeZero q] {z alpha y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - rowLambda r / Real.log z ≤ alpha) :
    DirichletZeroCount.familyCount q alpha y ≤ rowBound r := by
  have hl : 0.262132 ≤ rowLambda r := by cases r <;> norm_num [rowLambda]
  exact (familyCount_antitone_alpha ha).trans (effective_familyCount_bound r hz hqy hl le_rfl)

theorem low_height_familyCount_row (r : DensityRow) {q : ℕ} [NeZero q] {x alpha : ℝ}
    (hx : 100000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (ha : 1 - rowLambda r / Real.log x ≤ alpha) :
    DirichletZeroCount.familyCount q alpha (x / q) ≤ rowBound r := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  apply familyCount_row_tail r hx _ ha
  rw [max_eq_right ((le_div_iff₀ hq0).mpr (by simpa using hq))]
  exact le_of_eq (mul_div_cancel₀ x hq0.ne')

theorem complete_tail_count_row (r : DensityRow) {q : ℕ} [NeZero q] {z alpha y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - rowLambda r / Real.log z ≤ alpha) :
    (∑ χ : DirichletCharacter ℂ q,
      ∑ ρ ∈ (CompleteExpansion.zeroValues χ y).filter (fun ρ => alpha ≤ ρ.re),
        analyticOrderNatAt χ.LFunction ρ) ≤ rowBound r := by
  have hhalf : 1 / 2 ≤ alpha :=
    (source_alpha_ge_half hz (row_basic_certificate r).2.1).trans ha
  rw [← DirichletZeroCount.Applications.familyCount_eq_complete_filter q hhalf]
  exact familyCount_row_tail r hz hqy ha

theorem family_band_weighted_row (r : DensityRow) {q : ℕ} [NeZero q]
    {z alpha u y M : ℝ} (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - rowLambda r / Real.log z ≤ alpha) (hM : 0 ≤ M)
    (f : DirichletCharacter ℂ q → ℂ → ℝ)
    (hf : ∀ χ ρ, ρ ∈ DirichletZeroCount.bandValues χ alpha u y → f χ ρ ≤ M) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ DirichletZeroCount.bandValues χ alpha u y,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) * f χ ρ) ≤ M * rowBound r := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
    (fun χ _ => DirichletZeroCount.band_weighted_sum_le_count χ alpha u y (f χ) hM (hf χ))
  rw [← Finset.mul_sum, ← Nat.cast_sum] at hh
  have hc : (DirichletZeroCount.familyCount q alpha y : ℝ) ≤ rowBound r := by
    exact_mod_cast familyCount_row_tail r hz hqy ha
  exact hh.trans (mul_le_mul_of_nonneg_left hc hM)

theorem family_inverse_band_row (r : DensityRow) {q : ℕ} [NeZero q] {z alpha u y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - rowLambda r / Real.log z ≤ alpha) (hu : 0 < u) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ DirichletZeroCount.bandValues χ alpha u y,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) / |ρ.im|) ≤ (rowBound r : ℝ) / u := by
  simpa only [mul_one_div, one_div_mul_eq_div] using
    family_band_weighted_row r hz hqy ha (by positivity : (0 : ℝ) ≤ 1 / u)
      (fun _ ρ => 1 / |ρ.im|) (fun _ _ hρ =>
        one_div_le_one_div_of_le hu (DirichletZeroCount.mem_bandValues.mp hρ).2.2.2)

theorem family_inverse_sqrt_band_row (r : DensityRow) {q : ℕ} [NeZero q] {z alpha u y : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ha : 1 - rowLambda r / Real.log z ≤ alpha) (hu : 0 < u) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ DirichletZeroCount.bandValues χ alpha u y,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) / Real.sqrt |ρ.im|) ≤
        (rowBound r : ℝ) / Real.sqrt u := by
  simpa only [mul_one_div, one_div_mul_eq_div] using
    family_band_weighted_row r hz hqy ha (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt u)
      (fun _ ρ => 1 / Real.sqrt |ρ.im|) (fun _ _ hρ =>
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr hu)
          (Real.sqrt_le_sqrt (DirichletZeroCount.mem_bandValues.mp hρ).2.2.2))

end LiuWang.Proof.NearOneDensity.Continuation
