import LiuWang.Proof.NonprincipalPsi.ZeroTransport
import LiuWang.Proof.PrincipalPsi.Quantitative.IndexTransport

/-!
# Ordinary L zeros in the full closed-height critical strip

Companion (3.2) has `alpha <= Re rho < 1`, not a strict alpha boundary.
For `0 < alpha < 1`, the additional explicit `0 < Re rho` is redundant.
Finiteness comes from the existing bounded divisor truncations, not a hypothesis.
The count below uses the ordinary L function's actual analytic multiplicity.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.FixedHeightZeroSum
open BombieriVinogradov.SiegelWalfisz
open Complex.Hadamard

namespace LiuWang.Proof.DirichletZeroCount

theorem mem_fixed_all {q : ℕ} [NeZero q] (chi : Character q) (y : ℝ)
    (p : CompletedZeroIndex chi) :
    p ∈ fixedZeroIndices chi y ↔
      0 < (completedZeroValue p).re ∧ (completedZeroValue p).re < 1 ∧
        |(completedZeroValue p).im| ≤ y := by
  rw [fixedZeroIndices, Finset.mem_filter, mem_criticalStripZeroTruncation_iff]
  change ((0 < _ ∧ _ < 1 ∧ |(completedZeroValue p).im| < y + 1) ∧
    |(completedZeroValue p).im| ≤ y) ↔ _
  constructor
  · exact fun h => ⟨h.1.1, h.1.2.1, h.2⟩
  · rintro ⟨h0, h1, hy⟩
    exact ⟨⟨h0, h1, by linarith⟩, hy⟩

def nonprincipalIndices {q : ℕ} [NeZero q] (chi : Character q) (alpha y : ℝ) :=
  (fixedZeroIndices chi y).filter (fun p => alpha ≤ (completedZeroValue p).re)

def principalIndices (q : ℕ) [NeZero q] (alpha y : ℝ) :=
  (PrincipalPsi.closedZeroIndices q y).filter
    (fun p => alpha ≤ (PrincipalPsi.principalZeroValue p).re)

theorem mem_nonprincipalIndices {q : ℕ} [NeZero q] {chi : Character q}
    {alpha y : ℝ} {p : CompletedZeroIndex chi} :
    p ∈ nonprincipalIndices chi alpha y ↔
      (0 < (completedZeroValue p).re ∧ (completedZeroValue p).re < 1 ∧
        |(completedZeroValue p).im| ≤ y) ∧ alpha ≤ (completedZeroValue p).re := by
  simp only [nonprincipalIndices, Finset.mem_filter, mem_fixed_all]

theorem mem_principalIndices {q : ℕ} [NeZero q] {alpha y : ℝ}
    {p : PrincipalPsi.PrincipalZeroIndex q} :
    p ∈ principalIndices q alpha y ↔
      (0 < (PrincipalPsi.principalZeroValue p).re ∧
        (PrincipalPsi.principalZeroValue p).re < 1 ∧
        |(PrincipalPsi.principalZeroValue p).im| ≤ y) ∧
          alpha ≤ (PrincipalPsi.principalZeroValue p).re := by
  simp only [principalIndices, Finset.mem_filter, PrincipalPsi.mem_closedZeroIndices]

def nonprincipalValues {q : ℕ} [NeZero q] (chi : Character q) (alpha y : ℝ) :=
  (nonprincipalIndices chi alpha y).image completedZeroValue

def principalValues (q : ℕ) [NeZero q] (alpha y : ℝ) :=
  (principalIndices q alpha y).image PrincipalPsi.principalZeroValue

theorem nonprincipal_fiber_card {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} {rho : ℂ}
    (hrho : rho ∈ nonprincipalValues chi alpha y) :
    ((nonprincipalIndices chi alpha y).filter
      (fun p => completedZeroValue p = rho)).card =
        analyticOrderNatAt chi.LFunction rho := by
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  have hr := mem_nonprincipalIndices.mp hp
  have hre : 0 < rho.re := hpv ▸ hr.1.1
  have hr0 : rho ≠ 0 := by intro h; simp [h] at hre
  have hf : (nonprincipalIndices chi alpha y).filter
      (fun p => completedZeroValue p = rho) =
        divisorZeroIndex₀_fiberFinset (symmetricCompletedLFunction chi) rho := by
    ext a
    rw [Finset.mem_filter, mem_nonprincipalIndices, mem_divisorZeroIndex₀_fiberFinset]
    change (_ ∧ completedZeroValue a = rho) ↔ completedZeroValue a = rho
    refine and_iff_right_of_imp ?_
    intro ha
    simpa only [ha, hpv] using hr
  rw [hf, divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (differentiable_symmetricCompletedLFunction hchi) hr0,
    analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hchi hre]

theorem principal_fiber_card {q : ℕ} [NeZero q] {alpha y : ℝ} {rho : ℂ}
    (hrho : rho ∈ principalValues q alpha y) :
    ((principalIndices q alpha y).filter
      (fun p => PrincipalPsi.principalZeroValue p = rho)).card =
        analyticOrderNatAt (1 : Character q).LFunction rho := by
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  have hr := mem_principalIndices.mp hp
  have hre : 0 < rho.re := hpv ▸ hr.1.1
  have hre1 : rho.re < 1 := hpv ▸ hr.1.2.1
  have hr0 : rho ≠ 0 := by intro h; simp [h] at hre
  have hr1 : rho ≠ 1 := by intro h; simp [h] at hre1
  have hf : (principalIndices q alpha y).filter
      (fun p => PrincipalPsi.principalZeroValue p = rho) =
        divisorZeroIndex₀_fiberFinset (PrincipalPsi.regularizedPrincipal q) rho := by
    ext a
    rw [Finset.mem_filter, mem_principalIndices, mem_divisorZeroIndex₀_fiberFinset]
    change (_ ∧ PrincipalPsi.principalZeroValue a = rho) ↔
      PrincipalPsi.principalZeroValue a = rho
    refine and_iff_right_of_imp ?_
    intro ha
    simpa only [ha, hpv] using hr
  rw [hf, divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ q) hr0,
    PrincipalPsi.analyticOrderNatAt_regularized_eq_principal hr1]

theorem mem_nonprincipalValues {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} {rho : ℂ} :
    rho ∈ nonprincipalValues chi alpha y ↔
      chi.LFunction rho = 0 ∧ (0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ y) ∧
        alpha ≤ rho.re := by
  constructor
  · intro h
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp h
    have hz : chi.LFunction rho = 0 := by
      apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
      rw [← nonprincipal_fiber_card hchi h]
      exact (Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpv⟩⟩).ne'
    exact ⟨hz, by simpa only [hpv] using mem_nonprincipalIndices.mp hp⟩
  · rintro ⟨hz, ⟨hre, hre1, hy⟩, ha⟩
    have hr0 : rho ≠ 0 := by intro h; simp [h] at hre
    have hcomp : symmetricCompletedLFunction chi rho = 0 := by
      rw [symmetricCompletedLFunction,
        DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos chi hre,
        hz, zero_mul, mul_zero]
    obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
      (differentiable_symmetricCompletedLFunction hchi)
      ⟨2, symmetricCompletedLFunction_two_ne_zero hchi⟩ hr0 hcomp
    exact Finset.mem_image.mpr ⟨p, mem_nonprincipalIndices.mpr (by
      simpa only [show completedZeroValue p = rho from hp] using
        And.intro ⟨hre, hre1, hy⟩ ha), hp⟩

theorem mem_principalValues {q : ℕ} [NeZero q] {alpha y : ℝ} {rho : ℂ} :
    rho ∈ principalValues q alpha y ↔
      (1 : Character q).LFunction rho = 0 ∧
        (0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ y) ∧ alpha ≤ rho.re := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    exact ⟨PrincipalPsi.principal_zero_at_index p, mem_principalIndices.mp hp⟩
  · rintro ⟨hz, ⟨hre, hre1, hy⟩, ha⟩
    have hr0 : rho ≠ 0 := by intro h; simp [h] at hre
    have hr1 : rho ≠ 1 := by intro h; simp [h] at hre1
    have hreg : PrincipalPsi.regularizedPrincipal q rho = 0 := by
      rw [PrincipalPsi.regularizedPrincipal_eq hr1, hz, mul_zero]
    obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
      ⟨1, PrincipalPsi.regularizedPrincipal_one_ne_zero q⟩ hr0 hreg
    exact Finset.mem_image.mpr ⟨p, mem_principalIndices.mpr (by
      simpa only [show PrincipalPsi.principalZeroValue p = rho from hp] using
        And.intro ⟨hre, hre1, hy⟩ ha), hp⟩

def zeroValues {q : ℕ} [NeZero q] (chi : Character q) (alpha y : ℝ) : Finset ℂ :=
  if chi = 1 then principalValues q alpha y else nonprincipalValues chi alpha y

theorem mem_zeroValues {q : ℕ} [NeZero q] {chi : Character q} {alpha y : ℝ} {rho : ℂ} :
    rho ∈ zeroValues chi alpha y ↔
      chi.LFunction rho = 0 ∧ (0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ y) ∧
        alpha ≤ rho.re := by
  by_cases hc : chi = 1
  · subst chi
    simpa only [zeroValues, ↓reduceIte] using mem_principalValues
  · simpa only [zeroValues, if_neg hc] using mem_nonprincipalValues hc

theorem zeroValues_eq_source {q : ℕ} [NeZero q] (chi : Character q)
    {alpha : ℝ} (ha : 0 < alpha) (y : ℝ) :
    (zeroValues chi alpha y : Set ℂ) =
      {rho | chi.LFunction rho = 0 ∧ alpha ≤ rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ y} := by
  ext rho
  simp only [Finset.mem_coe, mem_zeroValues, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, ⟨_, h1, hy⟩, hα⟩
    exact ⟨hz, hα, h1, hy⟩
  · rintro ⟨hz, hα, h1, hy⟩
    exact ⟨hz, ⟨ha.trans_le hα, h1, hy⟩, hα⟩

def count {q : ℕ} [NeZero q] (chi : Character q) (alpha y : ℝ) : ℕ :=
  ∑ rho ∈ zeroValues chi alpha y, analyticOrderNatAt chi.LFunction rho

theorem count_nonprincipal {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (alpha y : ℝ) :
    count chi alpha y = (nonprincipalIndices chi alpha y).card := by
  unfold count
  simp only [zeroValues, if_neg hchi]
  calc
    _ = ∑ rho ∈ nonprincipalValues chi alpha y,
        ∑ _p ∈ (nonprincipalIndices chi alpha y).filter
          (fun p => completedZeroValue p = rho), (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      simp [nonprincipal_fiber_card hchi hrho]
    _ = _ := by
      unfold nonprincipalValues
      rw [Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
      simp

theorem count_principal (q : ℕ) [NeZero q] (alpha y : ℝ) :
    count (1 : Character q) alpha y = (principalIndices q alpha y).card := by
  unfold count
  simp only [zeroValues, ↓reduceIte]
  calc
    _ = ∑ rho ∈ principalValues q alpha y,
        ∑ _p ∈ (principalIndices q alpha y).filter
          (fun p => PrincipalPsi.principalZeroValue p = rho), (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      simp [principal_fiber_card hrho]
    _ = _ := by
      unfold principalValues
      rw [Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
      simp

end LiuWang.Proof.DirichletZeroCount
