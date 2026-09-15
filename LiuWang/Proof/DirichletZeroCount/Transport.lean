import LiuWang.Proof.DirichletZeroCount.Values

/-! # Exact primitive and zeta transports, including both closed boundaries -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount

theorem zeroValues_eq_primitive {q : ℕ} [NeZero q] (chi : Character q)
    [NeZero chi.conductor] (hchi : chi ≠ 1) (alpha y : ℝ) :
    zeroValues chi alpha y = zeroValues chi.primitiveCharacter alpha y := by
  ext rho
  rw [mem_zeroValues, mem_zeroValues]
  by_cases hr : 0 < rho.re
  · rw [LFunction_eq_primitive_mul_levelCorrection chi hchi rho, mul_eq_zero]
    simp only [levelCorrection_ne_zero_of_re_pos chi hr, or_false]
  · simp [hr]

theorem count_eq_primitive {q : ℕ} [NeZero q] (chi : Character q)
    [NeZero chi.conductor] (hchi : chi ≠ 1) (alpha y : ℝ) :
    count chi alpha y = count chi.primitiveCharacter alpha y := by
  unfold count
  rw [zeroValues_eq_primitive chi hchi]
  apply Finset.sum_congr rfl
  intro rho hrho
  exact analyticOrderNatAt_LFunction_eq_primitive chi hchi
    (mem_zeroValues.mp hrho).2.1.1

theorem zeroValues_principal_eq_zeta (q : ℕ) [NeZero q] (alpha y : ℝ) :
    zeroValues (1 : Character q) alpha y = zeroValues (1 : Character 1) alpha y := by
  ext rho
  rw [mem_zeroValues, mem_zeroValues, DirichletCharacter.LFunction_modOne_eq]
  by_cases hr : 0 < rho.re
  · by_cases hr1 : rho.re < 1
    · have h1 : rho ≠ 1 := by intro h; simp [h] at hr1
      rw [PrincipalPsi.principal_zero_iff_zeta_zero hr h1]
    · simp [hr1]
  · simp [hr]

theorem count_principal_eq_zeta (q : ℕ) [NeZero q] (alpha y : ℝ) :
    count (1 : Character q) alpha y = count (1 : Character 1) alpha y := by
  unfold count
  rw [zeroValues_principal_eq_zeta q]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hr := (mem_zeroValues.mp hrho).2.1
  have h1 : rho ≠ 1 := by intro h; simp [h] at hr
  rw [PrincipalPsi.analyticOrderNatAt_principal_eq_zeta hr.1 h1,
    DirichletCharacter.LFunction_modOne_eq]

theorem count_mono_height {q : ℕ} [NeZero q] (chi : Character q) (alpha : ℝ)
    {y z : ℝ} (hyz : y ≤ z) : count chi alpha y ≤ count chi alpha z := by
  apply Finset.sum_le_sum_of_subset
  intro rho hrho
  obtain ⟨hz, ⟨hr, hr1, hy⟩, ha⟩ := mem_zeroValues.mp hrho
  exact mem_zeroValues.mpr ⟨hz, ⟨hr, hr1, hy.trans hyz⟩, ha⟩

theorem count_antitone_alpha {q : ℕ} [NeZero q] (chi : Character q) (y : ℝ)
    {alpha beta : ℝ} (hab : alpha ≤ beta) :
    count chi beta y ≤ count chi alpha y := by
  apply Finset.sum_le_sum_of_subset
  intro rho hrho
  obtain ⟨hz, hr, hb⟩ := mem_zeroValues.mp hrho
  exact mem_zeroValues.mpr ⟨hz, hr, hab.trans hb⟩

theorem count_nonprincipal_quadratic {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) (alpha y : ℝ) :
    (count chi alpha y : ℝ) ≤ (y ^ 2 + 4) * (Real.log q / 2 + 15 / 2) := by
  rw [count_nonprincipal hchi]
  exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans
    (FixedHeightZeroSum.card_fixedZeroIndices_le hchi hprim y)

theorem count_conductor_quadratic {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (alpha y : ℝ) :
    (count chi alpha y : ℝ) ≤
      (y ^ 2 + 4) * (Real.log chi.conductor / 2 + 15 / 2) := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [count_eq_primitive chi hchi]
  exact count_nonprincipal_quadratic
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi)
    chi.primitiveCharacter_isPrimitive alpha y

theorem count_principal_quadratic (q : ℕ) [NeZero q] (alpha : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    (count (1 : Character q) alpha y : ℝ) ≤ (2 / 3) * y ^ 2 := by
  rw [count_principal_eq_zeta, count_principal]
  exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans
    (PrincipalPsi.Quantitative.principal_closed_card_le hy)

theorem count_principal_zero_height (q : ℕ) [NeZero q] (alpha : ℝ) :
    count (1 : Character q) alpha 0 = 0 := by
  have h := count_principal_quadratic q alpha (y := 0) le_rfl
  norm_num at h
  exact h

end LiuWang.Proof.DirichletZeroCount
