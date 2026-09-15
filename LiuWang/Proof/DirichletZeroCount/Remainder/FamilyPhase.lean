import LiuWang.Proof.DirichletZeroCount.Remainder.ClosedCount

/-! # All-height conductor and modulus consumers, retaining the paid principal branch -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem parityShift_primitive {q : ℕ} [NeZero q] (chi : Character q) :
    parityShift chi.primitiveCharacter = parityShift chi := by
  have he := chi.primitiveCharacter_apply_of_isCoprime
    (a := (-1 : ℤ)) (show IsCoprime (-1 : ℤ) (q : ℤ) from ⟨-1, 0, by ring⟩)
  simp only [Int.cast_neg, Int.cast_one] at he
  simp only [parityShift, DirichletCharacter.Even, he]
  rfl

theorem phaseCountBound_mono_modulus {d q : ℕ} (hd : 0 < d) (hdq : d ≤ q)
    {a y : ℝ} (hy : 0 ≤ y) : phaseCountBound d a y ≤ phaseCountBound q a y := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdqR : (d : ℝ) ≤ q := Nat.cast_le.mpr hdq
  have hlog := Real.log_le_log hdR hdqR
  have hlogpi := Real.log_le_log (div_pos hdR Real.pi_pos)
    (div_le_div_of_nonneg_right hdqR Real.pi_pos.le)
  unfold phaseCountBound horizontalFee
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have h1 := mul_le_mul_of_nonneg_left hlogpi hy
  have h2 := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 5 * Real.pi / 2 + 4 by positivity)
  nlinarith

theorem count_nonprincipal_phase_conductor {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 2 ≤ y) :
    (count chi alpha y : ℝ) ≤ phaseCountBound chi.conductor (parityShift chi) y := by
  simpa only [parityShift_primitive] using count_conductor_phase_le hchi ha hy

theorem count_nonprincipal_phase_modulus {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 2 ≤ y) :
    (count chi alpha y : ℝ) ≤ phaseCountBound q (parityShift chi) y :=
  (count_nonprincipal_phase_conductor hchi ha hy).trans
    (phaseCountBound_mono_modulus (Nat.pos_of_ne_zero chi.conductor_ne_zero)
      (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) (by linarith))

def allHeightPhaseBound (d : ℕ) (a y : ℝ) : ℝ :=
  if 2 ≤ y then min (nonprincipalBound d y) (phaseCountBound d a y)
  else nonprincipalBound d y

theorem count_nonprincipal_all_heights {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤ allHeightPhaseBound chi.conductor (parityShift chi) y := by
  unfold allHeightPhaseBound
  split_ifs with h
  · exact le_min (count_le_conductor hchi alpha hy) (count_nonprincipal_phase_conductor hchi ha h)
  · exact count_le_conductor hchi alpha hy

theorem allHeightPhaseBound_le_old (d : ℕ) (a y : ℝ) :
    allHeightPhaseBound d a y ≤ nonprincipalBound d y := by
  unfold allHeightPhaseBound
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem allHeightPhaseBound_mono_modulus {d q : ℕ} (hd : 0 < d) (hdq : d ≤ q)
    {a y : ℝ} (hy : 0 ≤ y) :
    allHeightPhaseBound d a y ≤ allHeightPhaseBound q a y := by
  unfold allHeightPhaseBound
  split_ifs
  · exact min_le_min (nonprincipalBound_mono hd hdq hy) (phaseCountBound_mono_modulus hd hdq hy)
  · exact nonprincipalBound_mono hd hdq hy

def phaseFamilyBound (q : ℕ) [NeZero q] (y : ℝ) : ℝ :=
  principalBound y + ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
    allHeightPhaseBound chi.conductor (parityShift chi) y

theorem familyCount_le_phaseFamilyBound (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) ≤ phaseFamilyBound q y := by
  unfold familyCount phaseFamilyBound
  rw [Nat.cast_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Character q))]
  have hp := count_principal_le q alpha hy
  have hn : (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, (count chi alpha y : ℝ)) ≤
      ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
        allHeightPhaseBound chi.conductor (parityShift chi) y :=
    Finset.sum_le_sum (fun chi hc => count_nonprincipal_all_heights (Finset.mem_erase.mp hc).1 ha hy)
  linarith

theorem phaseFamilyBound_le_old (q : ℕ) [NeZero q] (y : ℝ) :
    phaseFamilyBound q y ≤ familyBound q y := by
  unfold phaseFamilyBound familyBound
  exact add_le_add_right (Finset.sum_le_sum (fun chi _ => allHeightPhaseBound_le_old _ _ _)) _

theorem phaseFamilyBound_le_modulus (q : ℕ) [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    phaseFamilyBound q y ≤ principalBound y + (q.totient - 1 : ℕ) *
      max (allHeightPhaseBound q (1 / 2) y) (allHeightPhaseBound q (3 / 2) y) := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold phaseFamilyBound
  apply add_le_add_right
  calc
    _ ≤ ∑ _chi ∈ (Finset.univ : Finset (Character q)).erase 1,
        max (allHeightPhaseBound q (1 / 2) y) (allHeightPhaseBound q (3 / 2) y) := by
      apply Finset.sum_le_sum
      intro chi _
      apply (allHeightPhaseBound_mono_modulus (Nat.pos_of_ne_zero chi.conductor_ne_zero)
        (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) hy).trans
      unfold parityShift
      split_ifs
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = _ := by simp [hc]

theorem normalized_familyCount_le_phase (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) / q.totient ≤
      (principalBound y + (q.totient - 1 : ℕ) *
        max (allHeightPhaseBound q (1 / 2) y) (allHeightPhaseBound q (3 / 2) y)) / q.totient :=
  div_le_div_of_nonneg_right
    ((familyCount_le_phaseFamilyBound q ha hy).trans (phaseFamilyBound_le_modulus q hy))
    (Nat.cast_nonneg _)

end LiuWang.Proof.DirichletZeroCount.Remainder
