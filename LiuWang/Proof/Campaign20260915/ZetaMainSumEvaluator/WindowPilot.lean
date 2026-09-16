import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.ArithmeticPilot
import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowEvaluator

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator

open LiuWang.Proof.Campaign20260915.ZetaValidation

def boundaryPilot : WindowInput :=
  ⟨6, 7, 13 / 2, 1 / 2, 0, 0, 0, 1⟩

theorem boundaryPilot_output :
    checkedWindow 10 [] boundaryPilot = .ok (-2, 2) := by
  norm_num [checkedWindow, WindowReady, WindowChecks, boundaryPilot, CutoffWindow,
    piLower, piUpper, rationalPi20, windowCenter, windowRadius,
    evaluateEntries, radiusEntries]

theorem zeroGrid_rejected (entries : List SharedEntry) (r : WindowInput) :
    checkedWindow 0 entries r =
      .error "Invalid rounding grid, cache length, height/cutoff window, radius, or phase scale" := by
  simp [checkedWindow, WindowReady]

theorem zeroCacheGrid_rejected :
    checkedBatch 10 0 80 1 [boundaryPilot] =
      [.error "Reciprocal-square-root and logarithm grid must be positive"] := by
  simp [checkedBatch]

theorem invalidHeightRadius_rejected :
    checkedWindow 10 [] { boundaryPilot with heightRadius := 0 } =
      .error "Invalid rounding grid, cache length, height/cutoff window, radius, or phase scale" := by
  norm_num [checkedWindow, WindowReady, WindowChecks, boundaryPilot]

theorem boundaryPilot_source_enclosure {t : ℝ} (ht : 6 ≤ t ∧ t ≤ 7) :
    (-2 : ℝ) ≤ sourceMainSum t ∧ sourceMainSum t ≤ 2 := by
  have hb := cutoffWindow_bounds pilot_boundary_window (t := t) (by simpa using ht)
  have he := finiteMainSum_length_error t 0 (sourceCutoff t)
  have hn : (sourceCutoff t : ℝ) ≤ 1 := by exact_mod_cast hb.2
  simp only [Nat.zero_add, finiteMainSum, Finset.range_zero, Finset.sum_empty,
    sub_zero] at he
  change |sourceMainSum t| ≤ 2 * (sourceCutoff t : ℝ) at he
  rw [abs_le] at he
  constructor <;> linarith [he.1, he.2]

#print axioms boundaryPilot_output
#print axioms boundaryPilot_source_enclosure

end LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator
