import LiuWang.Proof.SourceRoute.Density.WeightedDetection
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.LittlewoodEntire
import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.LogBoundary

/-! The actual full nonprincipal counting inequality, with the horizontal cost retained. -/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans (nonprincipalRatio)
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.SourceRoute.Density

def horizontalDifference (q : ℕ) [NeZero q] (X a U : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q,
    ((∫ x in a..2, (horizontalLog (H chi X) 2 U U x).im) -
      (∫ x in a..2, (horizontalLog (H chi X) 2 U (-U) x).im))) / q.totient

theorem H_littlewood {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {a U : ℝ}
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    2 * Real.pi *
      (RectangleIntegral' (weightedKernel (H chi X) ((a : ℂ) - U * I))
        ((a : ℂ) - U * I) ((2 : ℂ) + U * I)).re =
      (∫ t in -U..U,
        (Real.log ‖H chi X ((a : ℂ) + t * I)‖ -
          Real.log ‖H chi X ((2 : ℂ) + t * I)‖)) +
      ((∫ x in a..2, (horizontalLog (H chi X) 2 U U x).im) -
        (∫ x in a..2, (horizontalLog (H chi X) 2 U (-U) x).im)) := by
  have h := rectangle_littlewood_entire (differentiable_H hchi X)
    (a := a) (b := 2) (c := -U) (d := U) (by simpa [sub_eq_add_neg] using hb)
  simp only [ofReal_neg, neg_mul, ← sub_eq_add_neg, ofReal_ofNat] at h
  have hi := intervalIntegral.integral_sub
    (log_H_vertical_integrable hchi X a U) (log_H_vertical_integrable hchi X 2 U)
  simp only [ofReal_ofNat] at hi
  rw [hi]
  exact h.trans (by ring)

theorem family_littlewood (q : ℕ) [NeZero q] (X : ℝ) {a U : ℝ}
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    2 * Real.pi * weightedContour q X a U =
      logSideDifference q X a U + horizontalDifference q X a U := by
  have h := Finset.sum_congr rfl (fun chi hchi =>
    H_littlewood ((mem_nonprincipalCharacters chi).mp hchi) X (hb chi hchi))
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at h
  unfold weightedContour logSideDifference horizontalDifference
  rw [← add_div, ← h]
  ring

theorem closed_count_littlewood (q : ℕ) [NeZero q] {X alpha T a U d : ℝ}
    (hX : 3 < X) (ha : a ≤ 2) (hU : 0 ≤ U) (hTU : T ≤ U)
    (hd : 0 ≤ d) (hgap : a + d ≤ alpha)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    2 * Real.pi * d * ((nonprincipalCount q alpha T : ℝ) / q.totient) ≤
      logSideDifference q X a U + horizontalDifference q X a U := by
  have h := mul_le_mul_of_nonneg_left
    (closed_count_weighted_le q hX ha hU hTU hd hgap hb)
    (by positivity : 0 ≤ 2 * Real.pi)
  rw [family_littlewood q X hb] at h
  simpa only [mul_assoc] using h

theorem closed_count_PV (q : ℕ) [NeZero q] {X alpha T a U d : ℝ}
    (hX : 5 ≤ X) {M : ℕ} (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    (ha : a ∈ Icc (1 / 2) 1) (hU : 0 ≤ U) (hTU : T ≤ U)
    (hd : 0 ≤ d) (hgap : a + d ≤ alpha)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    2 * Real.pi * d * ((nonprincipalCount q alpha T : ℝ) / q.totient) ≤
      pvBudget q X M a U + nonprincipalRatio q * (16 * U / (X - 1) ^ 2) +
        horizontalDifference q X a U :=
  (closed_count_littlewood q (by linarith) (by linarith [ha.2]) hU hTU hd hgap hb).trans
    (add_le_add (logSideDifference_PV q hX hNM hqN ha hU) le_rfl)

theorem produced_closed_count_PV (q : ℕ) [NeZero q] {X alpha T d e : ℝ}
    (hX : 5 ≤ X) {M : ℕ} (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    (halpha : alpha ≤ 1) (hleft : 1 / 2 ≤ alpha - d - e)
    (hT : 0 ≤ T) (hd : 0 < d) (he : 0 < e) :
    ∃ a ∈ Ioo (alpha - d - e) (alpha - d), ∃ U ∈ Ioo T (T + e),
      (∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) ∧
      2 * Real.pi * d * ((nonprincipalCount q alpha T : ℝ) / q.totient) ≤
        pvBudget q X M a U + nonprincipalRatio q * (16 * U / (X - 1) ^ 2) +
          horizontalDifference q X a U := by
  obtain ⟨a, ha, U, hU, hb⟩ :=
    family_boundary_perturbation q (by linarith : 3 < X) he (a := alpha - d) (T := T)
  refine ⟨a, ha, U, hU, hb, ?_⟩
  exact closed_count_PV q hX hNM hqN ⟨by linarith [ha.1], by linarith [ha.2]⟩
    (by linarith [hU.1]) hU.1.le hd.le (by linarith [ha.2]) hb

theorem produced_closed_count_PV_unnormalized (q : ℕ) [NeZero q] {X alpha T d e : ℝ}
    (hX : 5 ≤ X) {M : ℕ} (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    (halpha : alpha ≤ 1) (hleft : 1 / 2 ≤ alpha - d - e)
    (hT : 0 ≤ T) (hd : 0 < d) (he : 0 < e) :
    ∃ a ∈ Ioo (alpha - d - e) (alpha - d), ∃ U ∈ Ioo T (T + e),
      (∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) ∧
      2 * Real.pi * d * (nonprincipalCount q alpha T : ℝ) ≤
        (q.totient : ℝ) *
          (pvBudget q X M a U + nonprincipalRatio q * (16 * U / (X - 1) ^ 2) +
            horizontalDifference q X a U) := by
  obtain ⟨a, ha, U, hU, hb, h⟩ :=
    produced_closed_count_PV q hX hNM hqN halpha hleft hT hd he
  refine ⟨a, ha, U, hU, hb, ?_⟩
  have hp : (0 : ℝ) < q.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  rw [← mul_div_assoc] at h
  exact ((div_le_iff₀ hp).mp h).trans_eq (mul_comm _ _)

@[simp] theorem horizontalDifference_one (X a U : ℝ) :
    horizontalDifference 1 X a U = 0 := by simp [horizontalDifference]

@[simp] theorem horizontalDifference_two (X a U : ℝ) :
    horizontalDifference 2 X a U = 0 := by simp [horizontalDifference]

end LiuWang.Proof.SourceRoute.Density
