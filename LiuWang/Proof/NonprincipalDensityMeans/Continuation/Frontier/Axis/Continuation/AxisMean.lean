import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.Budget

/-! Actual fixed-X full-axis PV consumers, with exact phi recovery and comparison to frozen bounds. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

theorem exponential_PV_fixed_X (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    exponentialMean q ((q : ℝ) * y) sigma y ≤ 16 * pvBudget q ((q : ℝ) * y) M sigma y :=
  (exponential_family_of_windows q ((q : ℝ) * y) sigma (by linarith)
    (fun _ hu => Fmean_PV_all_heights q hy hs hu hNM)).2

theorem cosine_PV_fixed_X (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    cosineMean q ((q : ℝ) * y) sigma y ≤ 256 * pvBudget q ((q : ℝ) * y) M sigma y := by
  have h := cosineMean_le_exponential q ((q : ℝ) * y) hy
    (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩) (fun chi hchi =>
      exponential_strip_integrable ((mem_nonprincipalCharacters chi).mp hchi) _ (by linarith) hs.1)
  exact h.trans ((mul_le_mul_of_nonneg_left (exponential_PV_fixed_X q hy hs hNM)
    (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

theorem Fmean_PV_axis_recovery (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    Fmean q ((q : ℝ) * y) sigma y ≤ 768 * pvBudget q ((q : ℝ) * y) M sigma y :=
  (Fmean_le_cosineMean q _ hy hs).trans ((mul_le_mul_of_nonneg_left
    (cosine_PV_fixed_X q hy hs hNM) (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))

theorem PV_same_object_comparisons (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    (Fmean q ((q : ℝ) * y) sigma y ≤ pvBudget q ((q : ℝ) * y) M sigma y ∧
      pvBudget q ((q : ℝ) * y) M sigma y ≤ intermediateBudget q ((q : ℝ) * y) M sigma y) ∧
    (exponentialMean q ((q : ℝ) * y) sigma y ≤ 16 * pvBudget q ((q : ℝ) * y) M sigma y ∧
      16 * pvBudget q ((q : ℝ) * y) M sigma y ≤ 16 * intermediateBudget q ((q : ℝ) * y) M sigma y) ∧
    (cosineMean q ((q : ℝ) * y) sigma y ≤ 256 * pvBudget q ((q : ℝ) * y) M sigma y ∧
      256 * pvBudget q ((q : ℝ) * y) M sigma y ≤ 256 * intermediateBudget q ((q : ℝ) * y) M sigma y) := by
  have h := pvBudget_le_old q ((q : ℝ) * y) M sigma (by linarith : 0 ≤ y)
  exact ⟨⟨Fmean_PV_fixed_X q hy hs hNM, h⟩,
    ⟨exponential_PV_fixed_X q hy hs hNM, mul_le_mul_of_nonneg_left h (by norm_num)⟩,
    ⟨cosine_PV_fixed_X q hy hs hNM, mul_le_mul_of_nonneg_left h (by norm_num)⟩⟩

theorem Fmean_PV_unnormalized (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
        (q.totient : ℝ) * pvBudget q ((q : ℝ) * y) M sigma y := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  exact ((div_le_iff₀ hp).mp (Fmean_PV_fixed_X q hy hs hNM)).trans_eq (mul_comm _ _)

theorem exponential_PV_unnormalized (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y)) ≤ (q.totient : ℝ) * (16 * pvBudget q ((q : ℝ) * y) M sigma y) :=
  exponentialMean_unnormalized q _ sigma y _ (exponential_PV_fixed_X q hy hs hNM)

theorem cosine_PV_unnormalized (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
        (q.totient : ℝ) * (256 * pvBudget q ((q : ℝ) * y) M sigma y) := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  exact ((div_le_iff₀ hp).mp (cosine_PV_fixed_X q hy hs hNM)).trans_eq (mul_comm _ _)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation
