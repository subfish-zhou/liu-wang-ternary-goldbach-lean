import LiuWang.Proof.DirichletZeroCount.Argument.CompletedCount

/-! # Reflection transports the left three sides to the negative conjugate -/

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate
open LiuWang.Proof.Interfaces (Character)
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Argument

def rightThreeIntegral (g : ℂ → ℂ) (b H : ℝ) : ℂ :=
  HIntegral g (1 / 2) b (-H) + VIntegral g b (-H) H - HIntegral g (1 / 2) b H

theorem horizontal_reflection {g : ℂ → ℂ}
    (hg : ∀ s, g (1 - conj s) = -conj (g s)) (b t : ℝ) :
    HIntegral g (1 - b) (1 / 2) t = -conj (HIntegral g (1 / 2) b t) := by
  have hp (x : ℝ) : g ((1 - x : ℝ) + (t : ℂ) * I) =
      -conj (g ((x : ℂ) + (t : ℂ) * I)) := by
    convert hg ((x : ℂ) + (t : ℂ) * I) using 1
    congr 1
    push_cast
    simp
    ring
  unfold HIntegral
  have hc := intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => g ((x : ℂ) + (t : ℂ) * I)) (a := 1 / 2) (b := b) 1
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hc
  rw [← hc]
  simp_rw [hp]
  rw [intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]

theorem vertical_reflection {g : ℂ → ℂ}
    (hg : ∀ s, g (1 - conj s) = -conj (g s)) (b H : ℝ) :
    VIntegral g (1 - b) (-H) H = conj (VIntegral g b (-H) H) := by
  have hp (t : ℝ) : g ((1 - b : ℝ) + (t : ℂ) * I) =
      -conj (g ((b : ℂ) + (t : ℂ) * I)) := by
    convert hg ((b : ℂ) + (t : ℂ) * I) using 1
    congr 1
    push_cast
    simp
    ring
  unfold VIntegral
  simp_rw [hp]
  rw [intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]
  simp

theorem horizontal_split {g : ℂ → ℂ} {b t : ℝ} (hb : 1 < b)
    (hi : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (t : ℂ) * I))
      volume (1 - b) b) :
    HIntegral g (1 - b) b t =
      HIntegral g (1 - b) (1 / 2) t + HIntegral g (1 / 2) b t := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.uIcc (1 - b) b := by
    rw [Set.uIcc_of_le (by linarith)]
    constructor <;> linarith
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hi.mono (Set.uIcc_subset_uIcc Set.left_mem_uIcc hhalf) le_rfl)
    (hi.mono (Set.uIcc_subset_uIcc hhalf Set.right_mem_uIcc) le_rfl)).symm

theorem rectangle_eq_right_sub_conj {g : ℂ → ℂ} {b H : ℝ} (hb : 1 < b)
    (hg : ∀ s, g (1 - conj s) = -conj (g s))
    (hi : RectangleBorderIntegrable g (lowerCorner b H) (upperCorner b H)) :
    RectangleIntegral g (lowerCorner b H) (upperCorner b H) =
      rightThreeIntegral g b H - conj (rightThreeIntegral g b H) := by
  have hbot : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (-H : ℝ) * I))
      volume (1 - b) b := by simpa [lowerCorner, upperCorner] using hi.1
  have htop : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (H : ℂ) * I))
      volume (1 - b) b := by simpa [lowerCorner, upperCorner] using hi.2.1
  simp only [RectangleIntegral, lowerCorner, upperCorner]
  simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im,
    I_re, I_im, mul_zero, mul_one, sub_zero, zero_sub, add_zero, zero_add]
  rw [horizontal_split hb hbot, horizontal_split hb htop,
    horizontal_reflection hg, horizontal_reflection hg, vertical_reflection hg]
  simp only [rightThreeIntegral, map_sub, map_add]
  ring

theorem logDeriv_border_integrable {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z w : ℂ}
    (hn : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleBorderIntegrable (logDeriv f) z w := by
  apply ContinuousOn.rectangleBorder_integrable
  intro s hs
  exact ((hf.analyticAt s).deriv.div (hf.analyticAt s) (hn s hs)).continuousAt.continuousWithinAt

theorem normalized_rectangle_eq_three_im {g : ℂ → ℂ} {b H : ℝ} (hb : 1 < b)
    (hg : ∀ s, g (1 - conj s) = -conj (g s))
    (hi : RectangleBorderIntegrable g (lowerCorner b H) (upperCorner b H)) :
    RectangleIntegral' g (lowerCorner b H) (upperCorner b H) =
      ((rightThreeIntegral g b H).im / Real.pi : ℝ) := by
  rw [RectangleIntegral', rectangle_eq_right_sub_conj hb hg hi]
  have hsub (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I := by
    apply Complex.ext <;> simp
    ring
  rw [hsub, smul_eq_mul]
  push_cast
  field_simp

theorem completed_count_eq_three_im {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    (count chi 0 H : ℝ) =
      (rightThreeIntegral (logDeriv (symmetricCompletedLFunction chi)) b H).im / Real.pi := by
  have hi := logDeriv_border_integrable (differentiable_symmetricCompletedLFunction hchi)
    (completed_border_nonzero hchi hprim hb hH hreg)
  have h := (completed_rectangle_count hchi hprim hb hH hreg).symm.trans
    (normalized_rectangle_eq_three_im hb (completed_logDeriv_reflection hchi hprim) hi)
  exact_mod_cast h

theorem completed_count_alpha_le_three_im {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {alpha b H : ℝ}
    (ha : 0 ≤ alpha) (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    (count chi alpha H : ℝ) ≤
      (rightThreeIntegral (logDeriv (symmetricCompletedLFunction chi)) b H).im / Real.pi :=
  (Nat.cast_le.mpr (count_antitone_alpha chi H ha)).trans_eq
    (completed_count_eq_three_im hchi hprim hb hH hreg)

theorem exists_completed_three_count {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b y r : ℝ}
    (hb : 1 < b) (hy : 0 ≤ y) (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧
      (count chi 0 y : ℝ) =
        (rightThreeIntegral (logDeriv (symmetricCompletedLFunction chi)) b H).im / Real.pi ∧
      ∀ alpha : ℝ, 0 ≤ alpha → (count chi alpha y : ℝ) ≤
        (rightThreeIntegral (logDeriv (symmetricCompletedLFunction chi)) b H).im / Real.pi := by
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  have hH := hy.trans hyH.le
  have hcount : (count chi 0 y : ℝ) =
      (rightThreeIntegral (logDeriv (symmetricCompletedLFunction chi)) b H).im / Real.pi := by
    rw [← hc chi 0 H hyH.le le_rfl]
    exact completed_count_eq_three_im hchi hprim hb hH (hreg chi)
  exact ⟨H, hyH, hHr, hcount, fun alpha ha =>
    (Nat.cast_le.mpr (count_antitone_alpha chi y ha)).trans_eq hcount⟩

end LiuWang.Proof.DirichletZeroCount.Argument
