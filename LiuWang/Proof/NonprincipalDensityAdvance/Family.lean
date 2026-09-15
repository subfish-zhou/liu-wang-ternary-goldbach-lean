import LiuWang.Proof.NonprincipalDensityAdvance.RightBoundary
import LiuWang.Proof.DirichletZeroCount.Family

/-!
# The full nonprincipal family and its actual zero multiplicities

No primitivity restriction, conductor collapse, or division by the number of
nonprincipal characters is made. The normalization is the ambient phi(q).
The detector comparison below is proved, not supplied as a density hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NonprincipalDensityAdvance

def nonprincipalCharacters (q : ℕ) [NeZero q] : Finset (Character q) :=
  univ.erase 1

theorem mem_nonprincipalCharacters {q : ℕ} [NeZero q] (chi : Character q) :
    chi ∈ nonprincipalCharacters q ↔ chi ≠ 1 := by
  simp [nonprincipalCharacters]

theorem card_nonprincipalCharacters (q : ℕ) [NeZero q] :
    (nonprincipalCharacters q).card = q.totient - 1 := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  simp [nonprincipalCharacters, hc]

@[simp] theorem nonprincipalCharacters_one : nonprincipalCharacters 1 = ∅ := by
  apply card_eq_zero.mp
  rw [card_nonprincipalCharacters]
  norm_num

@[simp] theorem nonprincipalCharacters_two : nonprincipalCharacters 2 = ∅ := by
  apply card_eq_zero.mp
  rw [card_nonprincipalCharacters]
  norm_num

def nonprincipalCount (q : ℕ) [NeZero q] (alpha y : ℝ) : ℕ :=
  ∑ chi ∈ nonprincipalCharacters q, DirichletZeroCount.count chi alpha y

@[simp] theorem nonprincipalCount_one (alpha y : ℝ) :
    nonprincipalCount 1 alpha y = 0 := by
  simp [nonprincipalCount]

@[simp] theorem nonprincipalCount_two (alpha y : ℝ) :
    nonprincipalCount 2 alpha y = 0 := by
  simp [nonprincipalCount]

theorem familyCount_split (q : ℕ) [NeZero q] (alpha y : ℝ) :
    DirichletZeroCount.familyCount q alpha y =
      DirichletZeroCount.count (1 : Character 1) alpha y + nonprincipalCount q alpha y := by
  rw [DirichletZeroCount.familyCount,
    ← sum_erase_add _ _ (mem_univ (1 : Character q)),
    DirichletZeroCount.count_principal_eq_zeta]
  exact Nat.add_comm _ _

theorem normalized_familyCount_split (q : ℕ) [NeZero q] (alpha y : ℝ) :
    (DirichletZeroCount.familyCount q alpha y : ℝ) / q.totient =
      (DirichletZeroCount.count (1 : Character 1) alpha y : ℝ) / q.totient +
        (nonprincipalCount q alpha y : ℝ) / q.totient := by
  rw [familyCount_split, Nat.cast_add, add_div]

theorem nonprincipalCount_eq_index_card_sum (q : ℕ) [NeZero q] (alpha y : ℝ) :
    nonprincipalCount q alpha y =
      ∑ chi ∈ nonprincipalCharacters q, (DirichletZeroCount.nonprincipalIndices chi alpha y).card := by
  apply sum_congr rfl
  intro chi hchi
  exact DirichletZeroCount.count_nonprincipal (mem_nonprincipalCharacters chi |>.mp hchi) alpha y

theorem nonprincipalCount_eq_multiplicity_sum (q : ℕ) [NeZero q] (alpha y : ℝ) :
    nonprincipalCount q alpha y =
      ∑ chi ∈ nonprincipalCharacters q, ∑ rho ∈ DirichletZeroCount.zeroValues chi alpha y,
        zeroMultiplicity chi rho := rfl

theorem detected_index_is_actual_zero {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} {p : CompletedZeroIndex chi}
    (hp : p ∈ DirichletZeroCount.nonprincipalIndices chi alpha y) (X : ℝ) :
    chi.LFunction (completedZeroValue p) = 0 ∧
      H chi X (completedZeroValue p) = 0 ∧
      alpha ≤ (completedZeroValue p).re ∧ (completedZeroValue p).re < 1 ∧
        |(completedZeroValue p).im| ≤ y := by
  have hv : completedZeroValue p ∈ DirichletZeroCount.nonprincipalValues chi alpha y :=
    mem_image.mpr ⟨p, hp, rfl⟩
  have hz := (DirichletZeroCount.mem_nonprincipalValues hchi).mp hv
  exact ⟨hz.1, H_eq_zero_of_LFunction_eq_zero hz.1 X,
    hz.2.2, hz.2.1.2.1, hz.2.1.2.2⟩

theorem analyticOrder_H_ne_top {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 3 < X) (s : ℂ) :
    analyticOrderAt (H chi X) s ≠ ⊤ :=
  Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero (differentiable_H hchi X)
    ⟨2, H_ne_zero_on_two chi (by norm_num) hX⟩ s

theorem multiplicity_le_detector {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 3 < X) (rho : ℂ) :
    zeroMultiplicity chi rho ≤ analyticOrderNatAt (H chi X) rho :=
  ENat.toNat_le_toNat (analyticOrder_H_ge_LFunction hchi X rho)
    (analyticOrder_H_ne_top hchi hX rho)

theorem nonprincipalCount_le_detector_orders (q : ℕ) [NeZero q]
    (alpha y : ℝ) {X : ℝ} (hX : 3 < X) :
    nonprincipalCount q alpha y ≤
      ∑ chi ∈ nonprincipalCharacters q, ∑ rho ∈ DirichletZeroCount.zeroValues chi alpha y,
        analyticOrderNatAt (H chi X) rho := by
  rw [nonprincipalCount_eq_multiplicity_sum]
  apply sum_le_sum
  intro chi hchi
  exact sum_le_sum fun rho _ =>
    multiplicity_le_detector (mem_nonprincipalCharacters chi |>.mp hchi) hX rho

theorem normalized_nonprincipalCount_le_detector_orders (q : ℕ) [NeZero q]
    (alpha y : ℝ) {X : ℝ} (hX : 3 < X) :
    (nonprincipalCount q alpha y : ℝ) / q.totient ≤
      (∑ chi ∈ nonprincipalCharacters q, ∑ rho ∈ DirichletZeroCount.zeroValues chi alpha y,
        (analyticOrderNatAt (H chi X) rho : ℝ)) / q.totient := by
  have h := Nat.cast_le (α := ℝ) |>.mpr (nonprincipalCount_le_detector_orders q alpha y hX)
  simp only [Nat.cast_sum] at h
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

theorem normalized_right_boundary_paid (q : ℕ) [NeZero q]
    {X : ℝ} (hX : 5 ≤ X) {u : ℝ} (hu : 0 ≤ u) :
    (∑ chi ∈ nonprincipalCharacters q,
      ∫ t in -u..u, |Real.log ‖H chi X ((2 : ℂ) + t * Complex.I)‖|) / q.totient ≤
        ((q.totient - 1 : ℕ) : ℝ) / q.totient * (16 * u / (X - 1) ^ 2) := by
  have h := sum_le_sum (s := nonprincipalCharacters q) fun chi hchi =>
    abs_log_integral_two_le (mem_nonprincipalCharacters chi |>.mp hchi) hX hu
  rw [sum_const, nsmul_eq_mul, card_nonprincipalCharacters] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)).trans_eq (by ring)

end LiuWang.Proof.NonprincipalDensityAdvance
