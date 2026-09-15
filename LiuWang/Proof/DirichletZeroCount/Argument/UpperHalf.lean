import LiuWang.Proof.DirichletZeroCount.Argument.XiCount

/-! # Principal counting on the upper right two-edge path -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Argument

def upperRightIntegral (g : ℂ → ℂ) (b H : ℝ) : ℂ :=
  VIntegral g b 0 H - HIntegral g (1 / 2) b H

theorem horizontal_conjugate {g : ℂ → ℂ} (hg : ∀ s, g (conj s) = conj (g s))
    (a b H : ℝ) :
    HIntegral g a b (-H) = conj (HIntegral g a b H) := by
  have hp (x : ℝ) : g ((x : ℂ) + (-H : ℝ) * I) =
      conj (g ((x : ℂ) + (H : ℂ) * I)) := by
    simpa using hg ((x : ℂ) + (H : ℂ) * I)
  simp only [HIntegral, hp, intervalIntegral.intervalIntegral_conj]

theorem vertical_lower_conjugate {g : ℂ → ℂ}
    (hg : ∀ s, g (conj s) = conj (g s)) (b H : ℝ) :
    VIntegral g b (-H) 0 = -conj (VIntegral g b 0 H) := by
  have hp (t : ℝ) : g ((b : ℂ) + (-t : ℝ) * I) =
      conj (g ((b : ℂ) + (t : ℂ) * I)) := by
    simpa using hg ((b : ℂ) + (t : ℂ) * I)
  have hc := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => g ((b : ℂ) + (t : ℂ) * I)) (a := 0) (b := H) 0
  simp only [zero_sub, neg_zero] at hc
  unfold VIntegral
  rw [← hc]
  simp only [hp, intervalIntegral.intervalIntegral_conj]
  simp

theorem rightThree_eq_upper_sub_conj {g : ℂ → ℂ} {b H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ s, g (conj s) = conj (g s))
    (hi : IntervalIntegrable (fun t : ℝ => g ((b : ℂ) + (t : ℂ) * I)) volume (-H) H) :
    rightThreeIntegral g b H = upperRightIntegral g b H - conj (upperRightIntegral g b H) := by
  have hzero : (0 : ℝ) ∈ Set.uIcc (-H) H := by
    rw [Set.uIcc_of_le (by linarith)]
    constructor <;> linarith
  have hv : VIntegral g b (-H) H = VIntegral g b (-H) 0 + VIntegral g b 0 H := by
    unfold VIntegral
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hi.mono (Set.uIcc_subset_uIcc Set.left_mem_uIcc hzero) le_rfl)
      (hi.mono (Set.uIcc_subset_uIcc hzero Set.right_mem_uIcc) le_rfl), smul_add]
  rw [rightThreeIntegral, hv, horizontal_conjugate hg, vertical_lower_conjugate hg]
  simp only [upperRightIntegral, map_sub]
  ring

theorem principal_count_eq_upper_im (q : ℕ) [NeZero q] {b H : ℝ}
    (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H →
      (1 : Character q).LFunction s ≠ 0) :
    (count (1 : Character q) 0 H : ℝ) =
      2 * (upperRightIntegral (logDeriv riemannXi) b H).im / Real.pi := by
  have hi := logDeriv_border_integrable differentiable_riemannXi (xi_border_nonzero q hb hH hreg)
  have hiv : IntervalIntegrable (fun t : ℝ => logDeriv riemannXi ((b : ℂ) + (t : ℂ) * I))
      volume (-H) H := by simpa [lowerCorner, upperCorner] using hi.2.2.1
  rw [principal_count_eq_three_im q hb hH hreg,
    rightThree_eq_upper_sub_conj hH xi_logDeriv_conjugate hiv]
  simp only [sub_im, conj_im]
  ring

theorem exists_principal_upper_count (q : ℕ) [NeZero q] {b y r : ℝ}
    (hb : 1 < b) (hy : 0 ≤ y) (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧
      (count (1 : Character q) 0 y : ℝ) =
        2 * (upperRightIntegral (logDeriv riemannXi) b H).im / Real.pi ∧
      ∀ alpha : ℝ, 0 ≤ alpha → (count (1 : Character q) alpha y : ℝ) ≤
        2 * (upperRightIntegral (logDeriv riemannXi) b H).im / Real.pi := by
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  have he : (count (1 : Character q) 0 y : ℝ) =
      2 * (upperRightIntegral (logDeriv riemannXi) b H).im / Real.pi := by
    rw [← hc 1 0 H hyH.le le_rfl]
    exact principal_count_eq_upper_im q hb (hy.trans hyH.le) (hreg 1)
  exact ⟨H, hyH, hHr, he, fun alpha ha =>
    (Nat.cast_le.mpr (count_antitone_alpha (1 : Character q) y ha)).trans_eq he⟩

end LiuWang.Proof.DirichletZeroCount.Argument
