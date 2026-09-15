import LiuWang.Proof.NearOneDensity.Main

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NearOneDensity

example {q : ℕ} [NeZero q] (y : ℝ) (p : ZeroIndex q) :
    p ∈ zeroFamily q (1 - 0.5 / Real.log 100000000000) y ↔
      p.1.LFunction p.2.1 = 0 ∧ 1 - 0.5 / Real.log 100000000000 ≤ p.2.1.re ∧
        p.2.1.re < 1 ∧ |p.2.1.im| ≤ y :=
  source_mem_zeroFamily (by norm_num) (by norm_num) p

example (α y : ℝ) :
    zeroCount 1 α y =
      ∑ χ : Character 1, ∑ ρ ∈ zeroValues χ α y, analyticOrderNatAt χ.LFunction ρ :=
  zeroCount_eq_multiplicity_sum 1 α y

example {q : ℕ} [NeZero q] (χ : Character q) {ρ : ℂ}
    (hz : χ.LFunction ρ = 0) (hre : 1 - 0.262132 / Real.log 100000000000 ≤ ρ.re)
    (hlt : ρ.re < 1) :
    ∃ p ∈ zeroFamily q (1 - 0.262132 / Real.log 100000000000) |ρ.im|,
      p.1 = χ ∧ p.2.1 = ρ :=
  ordinary_zero_has_index (source_alpha_ge_half (by norm_num) (by norm_num))
    hz hre hlt le_rfl

example : rowBound .r045 = 182 ∧ rowBound .r046 = 292 ∧ rowBound .r047 = 664 ∧
    rowBound .r0475 = 1668 ∧ rowBound .r0478 = 14000 := by
  norm_num [rowBound, rowMultiplicity, rowSelectedBound]

example : 0 ≤ massBudget 0.311 (1 / Real.log 100000000000) ∧
    crossBudget ((1 - 1 / Real.sqrt 5) / 2) (1 / Real.log 100000000000) ≤
      massBudget 0.311 (1 / Real.log 100000000000) := by
  have h := row_source_budget .r0478 (z := 100000000000) (lam := 0.478)
    (by norm_num) (by norm_num) (by norm_num [rowLambda])
  exact ⟨h.1, h.2.1⟩

example {ι κ : Type*} (s : Finset ι) (label : ι → κ) (height : ι → ℝ) {b : ℝ}
    (hb : 0 ≤ b)
    (h : ∀ k t, (s.filter (fun i => label i = k ∧ |height i - t| ≤ b)).card ≤ 2) :
    ∃ u ⊆ s, s.card ≤ 2 * u.card ∧
      ∀ i ∈ u, ∀ j ∈ u, i ≠ j → label i = label j → 2 * b < |height i - height j| :=
  exists_separated_subfamily s label height hb 2 h
