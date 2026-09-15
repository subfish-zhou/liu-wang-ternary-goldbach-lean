import LiuWang.Proof.DirichletZeroCount.Remainder.XiHorizontal

/-! # Actual principal counts with all contour costs at the original closed height -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def xiPhaseCountBound (y : ℝ) : ℝ :=
  (3 * Real.pi + sourceGammaMain 4 y - y * Real.log Real.pi + 2 * xiHorizontalFee y) / Real.pi

theorem xiHorizontalFee_continuous : Continuous xiHorizontalFee := by
  have hl : Continuous (fun H : ℝ => Real.log (|H| + 2)) :=
    (show Continuous (fun H : ℝ => |H| + 2) by fun_prop).log
      (fun H => ne_of_gt (by positivity : 0 < |H| + 2))
  unfold xiHorizontalFee
  fun_prop

theorem xiPhaseCountBound_continuous : Continuous xiPhaseCountBound := by
  have hg := sourceGammaMain_continuous (a := 4) (by norm_num)
  have hh := xiHorizontalFee_continuous
  unfold xiPhaseCountBound
  fun_prop

theorem principal_count_regular_le_phase (q : ℕ) [NeZero q] {H : ℝ} (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → (1 : Character q).LFunction s ≠ 0) :
    (count (1 : Character q) 0 H : ℝ) ≤ xiPhaseCountBound H := by
  apply (principal_count_le_xi_horizontal q hH hreg).trans
  unfold xiPhaseCountBound
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have hh := (abs_le.mp (xi_horizontal_im_abs_le_regular q hH hreg)).1
  linarith

theorem principal_count_closed_le_phase (q : ℕ) [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    (count (1 : Character q) 0 y : ℝ) ≤ xiPhaseCountBound y := by
  by_contra hn
  have hl : xiPhaseCountBound y < (count (1 : Character q) 0 y : ℝ) := lt_of_not_ge hn
  have hmem := xiPhaseCountBound_continuous.continuousAt.preimage_mem_nhds (Iio_mem_nhds hl)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  have hclose : H ∈ Metric.ball y r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hyH)]
    linarith
  have hb := principal_count_regular_le_phase q (hy.trans hyH.le) (hreg 1)
  rw [hc 1 0 H hyH.le le_rfl] at hb
  exact (not_lt_of_ge hb) (hsub hclose)

theorem principal_count_alpha_le_phase (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (count (1 : Character q) alpha y : ℝ) ≤ xiPhaseCountBound y :=
  (Nat.cast_le.mpr (count_antitone_alpha (1 : Character q) y ha)).trans
    (principal_count_closed_le_phase q hy)

def principalPhaseBound (y : ℝ) : ℝ := min (principalBound y) (xiPhaseCountBound y)

def bothPhaseFamilyBound (q : ℕ) [NeZero q] (y : ℝ) : ℝ :=
  principalPhaseBound y + ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
    allHeightPhaseBound chi.conductor (parityShift chi) y

theorem familyCount_le_bothPhase (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) ≤ bothPhaseFamilyBound q y := by
  unfold familyCount bothPhaseFamilyBound
  rw [Nat.cast_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Character q))]
  have hp : (count (1 : Character q) alpha y : ℝ) ≤ principalPhaseBound y :=
    le_min (count_principal_le q alpha hy) (principal_count_alpha_le_phase q ha hy)
  have hn : (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, (count chi alpha y : ℝ)) ≤
      ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
        allHeightPhaseBound chi.conductor (parityShift chi) y :=
    Finset.sum_le_sum (fun chi hc => count_nonprincipal_all_heights (Finset.mem_erase.mp hc).1 ha hy)
  linarith

theorem bothPhaseFamilyBound_le_previous (q : ℕ) [NeZero q] (y : ℝ) :
    bothPhaseFamilyBound q y ≤ phaseFamilyBound q y := by
  exact add_le_add_left (min_le_left _ _) _

theorem normalized_familyCount_le_bothPhase (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) / q.totient ≤ bothPhaseFamilyBound q y / q.totient :=
  div_le_div_of_nonneg_right (familyCount_le_bothPhase q ha hy) (Nat.cast_nonneg _)

end LiuWang.Proof.DirichletZeroCount.Remainder
