import LiuWang.Proof.DirichletZeroCount.Argument.Rectangle
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLogDerivativeReflection

/-! # The actual primitive completed-L rectangle counts ordinary-L multiplicities -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators ComplexConjugate
open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Argument

theorem completed_zero_strip {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {s : ℂ}
    (hz : symmetricCompletedLFunction chi s = 0) : 0 < s.re ∧ s.re < 1 := by
  have hu : s.re < 1 := by
    by_contra h
    exact symmetricCompletedLFunction_ne_zero_of_one_le_re hchi (le_of_not_gt h) hz
  have hl : 0 < s.re := by
    by_contra h
    have hr : 1 ≤ (1 - conj s).re := by simp; linarith
    have href : symmetricCompletedLFunction chi (1 - conj s) = 0 := by
      rw [symmetricCompletedLFunction_one_sub_conj hchi hprim, hz, map_zero, mul_zero]
    exact symmetricCompletedLFunction_ne_zero_of_one_le_re hchi hr href
  exact ⟨hl, hu⟩

theorem completed_zero_iff_ordinary {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : 0 < s.re) :
    symmetricCompletedLFunction chi s = 0 ↔ chi.LFunction s = 0 := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [symmetricCompletedLFunction,
    DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos chi hs]
  simp only [mul_eq_zero, Complex.cpow_ne_zero_iff.mpr (Or.inl hq),
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hs, false_or, or_false]

theorem completed_border_nonzero {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    ∀ s ∈ RectangleBorder (lowerCorner b H) (upperCorner b H),
      symmetricCompletedLFunction chi s ≠ 0 := by
  intro s hs hz
  have hr := completed_zero_strip hchi hprim hz
  have hheight : |s.im| = H := by
    rcases (mem_border hb hH s).mp hs with ((hs | hs) | hs | hs)
    · rw [hs.2, abs_neg, abs_of_nonneg hH]
    · linarith [hs.1]
    · rw [hs.2, abs_of_nonneg hH]
    · linarith [hs.1]
  exact hreg s hr.1 hr.2 hheight ((completed_zero_iff_ordinary chi hr.1).mp hz)

theorem completed_rectangle_count {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    RectangleIntegral' (logDeriv (symmetricCompletedLFunction chi))
      (lowerCorner b H) (upperCorner b H) = (count chi 0 H : ℂ) := by
  have hV (s : ℂ) : s ∈ zeroValues chi 0 H ↔
      s ∈ Rectangle (lowerCorner b H) (upperCorner b H) ∧
        symmetricCompletedLFunction chi s = 0 := by
    rw [mem_zeroValues, mem_rectangle hb hH]
    constructor
    · rintro ⟨hz, ⟨h0, h1, ht⟩, _⟩
      exact ⟨⟨by linarith, by linarith, (abs_le.mp ht).1, (abs_le.mp ht).2⟩,
        (completed_zero_iff_ordinary chi h0).mpr hz⟩
    · rintro ⟨⟨_, _, hm, hp⟩, hz⟩
      have hr := completed_zero_strip hchi hprim hz
      exact ⟨(completed_zero_iff_ordinary chi hr.1).mp hz,
        ⟨hr.1, hr.2, abs_le.mpr ⟨hm, hp⟩⟩, hr.1.le⟩
  rw [entire_rectangle_count (differentiable_symmetricCompletedLFunction hchi)
    ⟨2, symmetricCompletedLFunction_two_ne_zero hchi⟩
    (by simp [lowerCorner, upperCorner]; linarith)
    (by simp [lowerCorner, upperCorner]; linarith) (zeroValues chi 0 H) hV
    (completed_border_nonzero hchi hprim hb hH hreg)]
  simp only [count, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hchi (mem_zeroValues.mp hs).2.1.1]

theorem completed_logDeriv_reflection {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) (s : ℂ) :
    logDeriv (symmetricCompletedLFunction chi) (1 - conj s) =
      -conj (logDeriv (symmetricCompletedLFunction chi) s) := by
  rw [logDeriv_symmetricCompletedLFunction_one_sub hchi hprim,
    logDeriv_symmetricCompletedLFunction_inv_eq_conj_conj hchi]
  simp

theorem exists_completed_rectangle_count {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b y r : ℝ}
    (hb : 1 < b) (hy : 0 ≤ y) (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧
      count chi 0 H = count chi 0 y ∧
      (∀ s ∈ RectangleBorder (lowerCorner b H) (upperCorner b H),
        symmetricCompletedLFunction chi s ≠ 0) ∧
      RectangleIntegral' (logDeriv (symmetricCompletedLFunction chi))
        (lowerCorner b H) (upperCorner b H) = (count chi 0 y : ℂ) := by
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  have hH : 0 ≤ H := hy.trans hyH.le
  have hcount := hc chi 0 H hyH.le le_rfl
  exact ⟨H, hyH, hHr, hcount, completed_border_nonzero hchi hprim hb hH (hreg chi),
    (completed_rectangle_count hchi hprim hb hH (hreg chi)).trans (congrArg Nat.cast hcount)⟩

end LiuWang.Proof.DirichletZeroCount.Argument
