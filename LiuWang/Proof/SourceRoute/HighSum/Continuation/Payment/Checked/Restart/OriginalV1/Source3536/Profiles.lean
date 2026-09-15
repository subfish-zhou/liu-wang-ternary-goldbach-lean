import LiuWang.Proof.SourceRoute.HighSum.Continuation.LogHeight
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Kernel

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

def c1 : ℝ := 9.645908801

def lower (L : ℝ) : ℝ := Real.log (3.36 * L ^ 3)

def upper (L : ℝ) : ℝ := Real.log (L ^ 3 * L ^ 15)

def profile35 (L s : ℝ) : ℝ :=
  2 * Real.exp (-L / (c1 * s)) + 11 * Real.exp (-0.3221 * L / s) +
    7 * Real.exp (-0.33 * L / s) - 20 * Real.exp (-0.36 * L / s)

def profile36 (L s : ℝ) : ℝ :=
  2 * Real.exp (-0.12 * L / s) + 6 * Real.exp (-0.2743 * L / s) +
    Real.exp (-0.28 * L / s) + Real.exp (-0.3 * L / s) +
    Real.exp (-0.31 * L / s) + 2 * Real.exp (-0.32 * L / s) +
    7 * Real.exp (-0.33 * L / s) - 20 * Real.exp (-0.36 * L / s)

def integrand (f : ℝ → ℝ → ℝ) (L s : ℝ) : ℝ :=
  L ^ 4 * Real.exp (-s) * f L s

def scalar35 (L : ℝ) : ℝ := ∫ s in lower L..upper L, integrand profile35 L s

def scalar36 (L : ℝ) : ℝ := ∫ s in lower L..upper L, integrand profile36 L s

theorem scalar35_literal (L : ℝ) :
    scalar35 L = ∫ s in Real.log (3.36 * L ^ 3)..Real.log (L ^ 3 * L ^ 15),
      L ^ 4 * Real.exp (-s) *
        (2 * Real.exp (-L / (9.645908801 * s)) +
          11 * Real.exp (-0.3221 * L / s) + 7 * Real.exp (-0.33 * L / s) -
            20 * Real.exp (-0.36 * L / s)) := rfl

theorem scalar36_literal (L : ℝ) :
    scalar36 L = ∫ s in Real.log (3.36 * L ^ 3)..Real.log (L ^ 3 * L ^ 15),
      L ^ 4 * Real.exp (-s) *
        (2 * Real.exp (-0.12 * L / s) + 6 * Real.exp (-0.2743 * L / s) +
          Real.exp (-0.28 * L / s) + Real.exp (-0.3 * L / s) +
          Real.exp (-0.31 * L / s) + 2 * Real.exp (-0.32 * L / s) +
          7 * Real.exp (-0.33 * L / s) - 20 * Real.exp (-0.36 * L / s)) := rfl

theorem c1_bounds : 0 < 1 / c1 ∧ 1 / c1 < 0.12 ∧ (0.1 : ℝ) ≤ 1 / c1 := by
  norm_num [c1]

theorem profile35_segments {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    profile35 L s =
      2 * lambdaSegment L s (1 / c1) 0.3221 +
        13 * lambdaSegment L s 0.3221 0.33 + 20 * lambdaSegment L s 0.33 0.36 := by
  rw [source35_signed_segments hL hs]
  unfold profile35
  congr 3
  ring

theorem profile36_segments {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    profile36 L s =
      2 * lambdaSegment L s 0.12 0.2743 +
        8 * lambdaSegment L s 0.2743 0.28 +
        9 * lambdaSegment L s 0.28 0.3 +
        10 * lambdaSegment L s 0.3 0.31 +
        11 * lambdaSegment L s 0.31 0.32 +
        13 * lambdaSegment L s 0.32 0.33 +
        20 * lambdaSegment L s 0.33 0.36 := by
  simp only [lambdaSegment_eq hL hs]
  unfold profile36
  ring

theorem segment_nonneg {L s a b : ℝ} (hL : 0 < L) (hs : 0 < s) (hab : a ≤ b) :
    0 ≤ lambdaSegment L s a b := by
  unfold lambdaSegment
  exact mul_nonneg (div_nonneg hL.le hs.le)
    (intervalIntegral.integral_nonneg_of_forall hab (fun _ => (Real.exp_pos _).le))

theorem profile35_nonneg {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    0 ≤ profile35 L s := by
  rw [profile35_segments hL hs]
  have h1 := segment_nonneg hL hs (show 1 / c1 ≤ 0.3221 by linarith [c1_bounds.2.1])
  have h2 := segment_nonneg hL hs (by norm_num : (0.3221 : ℝ) ≤ 0.33)
  have h3 := segment_nonneg hL hs (by norm_num : (0.33 : ℝ) ≤ 0.36)
  positivity

theorem profile36_nonneg {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    0 ≤ profile36 L s := by
  rw [profile36_segments hL hs]
  have h1 := segment_nonneg hL hs (by norm_num : (0.12 : ℝ) ≤ 0.2743)
  have h2 := segment_nonneg hL hs (by norm_num : (0.2743 : ℝ) ≤ 0.28)
  have h3 := segment_nonneg hL hs (by norm_num : (0.28 : ℝ) ≤ 0.3)
  have h4 := segment_nonneg hL hs (by norm_num : (0.3 : ℝ) ≤ 0.31)
  have h5 := segment_nonneg hL hs (by norm_num : (0.31 : ℝ) ≤ 0.32)
  have h6 := segment_nonneg hL hs (by norm_num : (0.32 : ℝ) ≤ 0.33)
  have h7 := segment_nonneg hL hs (by norm_num : (0.33 : ℝ) ≤ 0.36)
  positivity

theorem profile35_continuousOn (L : ℝ) : ContinuousOn (profile35 L) (Set.Ioi 0) := by
  have hs : ∀ s ∈ Set.Ioi (0 : ℝ), s ≠ 0 := fun _ h => ne_of_gt h
  have hc : c1 ≠ 0 := by norm_num [c1]
  have hcs : ∀ s ∈ Set.Ioi (0 : ℝ), c1 * s ≠ 0 := fun s h => mul_ne_zero hc (hs s h)
  unfold profile35
  fun_prop

theorem profile36_continuousOn (L : ℝ) : ContinuousOn (profile36 L) (Set.Ioi 0) := by
  have hs : ∀ s ∈ Set.Ioi (0 : ℝ), s ≠ 0 := fun _ h => ne_of_gt h
  unfold profile36
  fun_prop

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
