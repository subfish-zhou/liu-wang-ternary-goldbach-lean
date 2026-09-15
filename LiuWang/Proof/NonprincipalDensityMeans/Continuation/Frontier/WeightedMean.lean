import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.WeightedRows

/-! # Fixed-q means with separate unweighted and index-weighted energies -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

def firstUnitEnergy (q : ℕ) [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ S, if IsUnit (n : ZMod q) then (n : ℝ) * ‖a n‖ ^ 2 else 0

theorem weighted_family_mean (q : ℕ) [NeZero q] {K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ (range K).erase 0) (hlow : ∀ n ∈ S, q ≤ n)
    (a : ℕ → ℂ) {y : ℝ} (hy : 0 ≤ y) :
    familyMean q S a (fun n => -Real.log n) y ≤
      2 * y * unitEnergy q S a +
        6 / (q : ℝ) * harmonicRange (K / q + 1) * firstUnitEnergy q S a -
          principalMean q S a (fun n => -Real.log n) y := by
  have h := familyMean_diagonal_offDiagonal q S a (fun n => -Real.log n)
    ((negative_log_inj K).mono hS) hy
  have he (n m : ℕ) : |-Real.log n - -Real.log m| = |Real.log n - Real.log m| := by
    rw [show -Real.log n - -Real.log m = -(Real.log n - Real.log m) by ring, abs_neg]
  simp_rw [he] at h
  apply h.trans
  apply sub_le_sub_right
  calc
    _ ≤ ∑ x : ZMod q, if IsUnit x then
        2 * y * ∑ n ∈ fiber q S x, ‖a n‖ ^ 2 +
          6 / (q : ℝ) * harmonicRange (K / q + 1) *
            ∑ n ∈ fiber q S x, (n : ℝ) * ‖a n‖ ^ 2 else 0 := by
      apply sum_le_sum
      intro x _
      split_ifs
      · have hb := weighted_offDiagonal (hS.trans (erase_subset _ _)) hlow x a
        simp only [div_eq_mul_inv] at hb ⊢
        nlinarith only [hb]
      · rfl
    _ = _ := by
      have h0 := fiber_unit_sum q S (fun n => ‖a n‖ ^ 2)
      have h1 := fiber_unit_sum q S (fun n => (n : ℝ) * ‖a n‖ ^ 2)
      unfold unitEnergy firstUnitEnergy
      rw [← h0, ← h1]
      simp only [mul_sum]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro x _
      split_ifs
      · simp only [mul_sum]
      · simp

theorem weighted_dirichlet_mean (q : ℕ) [NeZero q] {K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ (range K).erase 0) (hlow : ∀ n ∈ S, q ≤ n)
    (c : ℕ → ℂ) (sigma : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖dirichletPolynomial chi S c ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient ≤
        2 * y * unitEnergy q S (verticalCoefficient c sigma) +
          6 / (q : ℝ) * harmonicRange (K / q + 1) *
            firstUnitEnergy q S (verticalCoefficient c sigma) -
        (∫ t in -y..y, ‖dirichletPolynomial (1 : Character q) S c
          ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient := by
  have hp : ∀ n ∈ S, 0 < n := fun _ hn => Nat.pos_of_ne_zero (mem_erase.mp (hS hn)).1
  simp_rw [dirichletPolynomial_eq_wave _ S hp]
  exact weighted_family_mean q hS hlow _ hy

theorem firstUnitEnergy_le (q : ℕ) [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) :
    firstUnitEnergy q S a ≤ ∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2 := by
  apply sum_le_sum
  intro n _
  split_ifs
  · rfl
  · positivity

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
