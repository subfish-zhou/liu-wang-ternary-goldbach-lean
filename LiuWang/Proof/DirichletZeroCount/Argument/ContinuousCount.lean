import LiuWang.Proof.DirichletZeroCount.Argument.Variation

/-! # Actual continuous logarithms on the three edges, with true zero-count increments -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open LiuWang.Proof.Interfaces (Character)
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Argument

def IsThreeLogLift (F : ℂ → ℂ) (b H : ℝ) (A B C : ℝ → ℂ) : Prop :=
  ContinuousOn A (Set.uIcc (1 / 2) b) ∧ ContinuousOn B (Set.uIcc (-H) H) ∧
  ContinuousOn C (Set.uIcc b (1 / 2)) ∧
  (∀ x ∈ Set.uIcc (1 / 2) b, exp (A x) = F ((x : ℂ) + (-H : ℝ) * I)) ∧
  (∀ t ∈ Set.uIcc (-H) H, exp (B t) = F ((b : ℂ) + (t : ℂ) * I)) ∧
  (∀ x ∈ Set.uIcc b (1 / 2), exp (C x) = F ((x : ℂ) + (H : ℂ) * I)) ∧
  A b = B (-H) ∧ B H = C b

theorem rightThree_nonzero {F : ℂ → ℂ} {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hn : ∀ s ∈ RectangleBorder (lowerCorner b H) (upperCorner b H), F s ≠ 0) :
    (∀ x ∈ Set.uIcc (1 / 2) b, F ((x : ℂ) + (-H : ℝ) * I) ≠ 0) ∧
    (∀ t ∈ Set.uIcc (-H) H, F ((b : ℂ) + (t : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.uIcc b (1 / 2), F ((x : ℂ) + (H : ℂ) * I) ≠ 0) := by
  have hhalf : (1 / 2 : ℝ) ≤ b := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Set.uIcc_of_le hhalf] at hx
    apply hn
    apply (mem_border hb hH _).mpr
    left; left
    simpa using And.intro (And.intro (by linarith [hx.1] : 1 - b ≤ x) hx.2) (rfl : -H = -H)
  · intro t ht
    rw [Set.uIcc_of_le (by linarith : -H ≤ H)] at ht
    apply hn
    apply (mem_border hb hH _).mpr
    right; right
    simpa using And.intro (rfl : b = b) ht
  · intro x hx
    rw [Set.uIcc_comm, Set.uIcc_of_le hhalf] at hx
    apply hn
    apply (mem_border hb hH _).mpr
    right; left
    simpa using And.intro (And.intro (by linarith [hx.1] : 1 - b ≤ x) hx.2) (rfl : H = H)

theorem exists_three_log_lift {F : ℂ → ℂ} (hF : Differentiable ℂ F) {b H : ℝ}
    (hb : 1 < b) (hH : 0 ≤ H)
    (hn : ∀ s ∈ RectangleBorder (lowerCorner b H) (upperCorner b H), F s ≠ 0) :
    ∃ A B C : ℝ → ℂ, IsThreeLogLift F b H A B C ∧
      C (1 / 2) - A (1 / 2) = rightThreeIntegral (logDeriv F) b H := by
  obtain ⟨hbot, hvert, htop⟩ := rightThree_nonzero hb hH hn
  let w := log (F (((1 / 2 : ℝ) : ℂ) + (-H : ℝ) * I))
  let A : ℝ → ℂ := fun x => w + lineLogIntegral F ((-H : ℝ) * I) 1 (1 / 2) x
  let B : ℝ → ℂ := fun t => A b + lineLogIntegral F b I (-H) t
  let C : ℝ → ℂ := fun x => B H + lineLogIntegral F ((H : ℂ) * I) 1 b x
  have hA := line_continuous_log_lift hF ((-H : ℝ) * I) 1
    (a := 1 / 2) (b := b)
    (by simpa [linePoint, add_comm] using hbot) w
    (by simpa [w, linePoint, add_comm] using exp_log (hbot (1 / 2) Set.left_mem_uIcc))
  have hB := line_continuous_log_lift hF (b : ℂ) I hvert (A b)
    (by simpa [A, linePoint, add_comm] using hA.2.1 b Set.right_mem_uIcc)
  have hC := line_continuous_log_lift hF ((H : ℂ) * I) 1
    (a := b) (b := 1 / 2)
    (by simpa [linePoint, add_comm] using htop) (B H)
    (by simpa [B, linePoint, add_comm] using hB.2.1 H Set.right_mem_uIcc)
  refine ⟨A, B, C, ?_, ?_⟩
  · refine ⟨hA.1, hB.1, hC.1, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [A, linePoint, add_comm] using hA.2.1
    · exact hB.2.1
    · simpa [C, linePoint, add_comm] using hC.2.1
    · simp [B, lineLogIntegral]
    · simp [C, lineLogIntegral]
  · simp only [A, B, C, lineLogIntegral, linePoint, mul_one, one_mul,
      intervalIntegral.integral_same, add_zero]
    rw [intervalIntegral.integral_const_mul]
    have hh : (∫ x : ℝ in b..(1 / 2), logDeriv F ((H : ℂ) * I + (x : ℂ))) =
        -HIntegral (logDeriv F) (1 / 2) b H := by
      rw [intervalIntegral.integral_symm]
      simp only [HIntegral, add_comm]
    rw [hh]
    simp only [rightThreeIntegral, HIntegral, VIntegral, smul_eq_mul, add_comm ((-H : ℝ) * I)]
    ring

theorem completed_count_continuous_argument {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    ∃ A B C : ℝ → ℂ, IsThreeLogLift (symmetricCompletedLFunction chi) b H A B C ∧
      (count chi 0 H : ℝ) = (C (1 / 2) - A (1 / 2)).im / Real.pi := by
  obtain ⟨A, B, C, hl, he⟩ := exists_three_log_lift
    (differentiable_symmetricCompletedLFunction hchi) hb hH
    (completed_border_nonzero hchi hprim hb hH hreg)
  exact ⟨A, B, C, hl, by rw [he]; exact completed_count_eq_three_im hchi hprim hb hH hreg⟩

theorem principal_count_continuous_argument (q : ℕ) [NeZero q] {b H : ℝ}
    (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H →
      (1 : Character q).LFunction s ≠ 0) :
    ∃ A B C : ℝ → ℂ, IsThreeLogLift riemannXi b H A B C ∧
      (count (1 : Character q) 0 H : ℝ) = (C (1 / 2) - A (1 / 2)).im / Real.pi := by
  obtain ⟨A, B, C, hl, he⟩ := exists_three_log_lift
    differentiable_riemannXi hb hH (xi_border_nonzero q hb hH hreg)
  exact ⟨A, B, C, hl, by rw [he]; exact principal_count_eq_three_im q hb hH hreg⟩

theorem exists_completed_continuous_count {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b y r : ℝ}
    (hb : 1 < b) (hy : 0 ≤ y) (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧ ∃ A B C : ℝ → ℂ,
      IsThreeLogLift (symmetricCompletedLFunction chi) b H A B C ∧
      (count chi 0 y : ℝ) = (C (1 / 2) - A (1 / 2)).im / Real.pi ∧
      ∀ alpha : ℝ, 0 ≤ alpha → (count chi alpha y : ℝ) ≤
        (C (1 / 2) - A (1 / 2)).im / Real.pi := by
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  obtain ⟨A, B, C, hl, he⟩ :=
    completed_count_continuous_argument hchi hprim hb (hy.trans hyH.le) (hreg chi)
  rw [hc chi 0 H hyH.le le_rfl] at he
  exact ⟨H, hyH, hHr, A, B, C, hl, he, fun alpha ha =>
    (Nat.cast_le.mpr (count_antitone_alpha chi y ha)).trans_eq he⟩

theorem exists_principal_continuous_count (q : ℕ) [NeZero q] {b y r : ℝ}
    (hb : 1 < b) (hy : 0 ≤ y) (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧ ∃ A B C : ℝ → ℂ,
      IsThreeLogLift riemannXi b H A B C ∧
      (count (1 : Character q) 0 y : ℝ) = (C (1 / 2) - A (1 / 2)).im / Real.pi ∧
      ∀ alpha : ℝ, 0 ≤ alpha → (count (1 : Character q) alpha y : ℝ) ≤
        (C (1 / 2) - A (1 / 2)).im / Real.pi := by
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  obtain ⟨A, B, C, hl, he⟩ := principal_count_continuous_argument q hb (hy.trans hyH.le) (hreg 1)
  rw [hc 1 0 H hyH.le le_rfl] at he
  exact ⟨H, hyH, hHr, A, B, C, hl, he, fun alpha ha =>
    (Nat.cast_le.mpr (count_antitone_alpha (1 : Character q) y ha)).trans_eq he⟩

end LiuWang.Proof.DirichletZeroCount.Argument
