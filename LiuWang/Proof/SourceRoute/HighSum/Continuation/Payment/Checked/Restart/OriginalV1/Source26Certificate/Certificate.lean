import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Arithmetic
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Uniform

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate

def point (i : ℕ) : ℚ :=
  if i ≤ 20 then 25 + 2 * i else if i = 21 then 70 else if i = 22 then 80 else 100

def cap (i : ℕ) : ℚ :=
  ([168, 1706, 10405, 41517, 115928, 239045, 380246, 483604, 506552, 447911,
    341344, 228158, 135763, 72839, 35623, 16032, 6695, 2612, 959, 333, 175, 15, 1] :
      List ℚ)[i]?.getD 0 / 10000000000

theorem point_domain (i : ℕ) (hi : i < 23) :
    0 < point i ∧ point i < point (i + 1) ∧ point (i + 1) ≤ 100 := by
  interval_cases i <;> norm_num [point]

theorem fixed_phases (i : ℕ) (hi : i < 23) :
    qPhase (point i) (point (i + 1)) (point i) ≤ 0 ∧
    qPhase (point i) (point (i + 1)) ((point i + point (i + 1)) / 2) ≤ 0 ∧
    qPhase (point i) (point (i + 1)) (point (i + 1)) ≤ 0 := by
  interval_cases i <;> norm_num [point, qPhase, qSlope, qA, qB]

theorem fixed_rational_bounds (i : ℕ) (hi : i < 23) :
    rationalRefined (point i) (point (i + 1)) ≤ cap i := by
  interval_cases i <;> norm_num [point, cap]
  · convert rational_cell_25 using 1; norm_num
  · convert rational_cell_27 using 1; norm_num
  · convert rational_cell_29 using 1; norm_num
  · exact rational_cell_31
  · convert rational_cell_33 using 1; norm_num
  · convert rational_cell_35 using 1; norm_num
  · convert rational_cell_37 using 1; norm_num
  · convert rational_cell_39 using 1; norm_num
  · convert rational_cell_41 using 1; norm_num
  · exact rational_cell_43
  · convert rational_cell_45 using 1; norm_num
  · convert rational_cell_47 using 1; norm_num
  · exact rational_cell_49
  · exact rational_cell_51
  · exact rational_cell_53
  · convert rational_cell_55 using 1; norm_num
  · convert rational_cell_57 using 1; norm_num
  · convert rational_cell_59 using 1; norm_num
  · exact rational_cell_61
  · exact rational_cell_63
  · convert rational_cell_65 using 1; norm_num
  · convert rational_cell_70 using 1; norm_num
  · exact rational_cell_80

theorem fixed_actual_bounds (i : ℕ) (hi : i < 23) :
    (∫ s in (point i : ℝ)..(point (i + 1) : ℝ), integrand 3100 s) ≤ (cap i : ℝ) := by
  have hd := point_domain i hi
  have hp := fixed_phases i hi
  exact (refined_le_rational hd.1 hd.2.1 hd.2.2 hp.1 hp.2.1 hp.2.2).trans
    (by exact_mod_cast fixed_rational_bounds i hi)

theorem fixed_core_paid :
    (∫ s in (25 : ℝ)..100, integrand 3100 s) ≤
      31 / 100000 - 1 / 1000000000000 := by
  have hb : (100 : ℝ) ≤ 18 * Real.log (3100 : ℝ) := by linarith [log_3100_bounds.1]
  have hi (i : ℕ) (hi : i < 23) :
      IntervalIntegrable (integrand 3100) volume (point i : ℝ) (point (i + 1) : ℝ) := by
    have hd := point_domain i hi
    apply integrand_integrable (by norm_num)
    · exact_mod_cast hd.1
    · exact_mod_cast hd.2.1.le
    · exact (show (point (i + 1) : ℝ) ≤ 100 by exact_mod_cast hd.2.2).trans hb
  have he := intervalIntegral.sum_integral_adjacent_intervals hi
  have h := Finset.sum_le_sum (s := Finset.range 23)
    (fun i hi => fixed_actual_bounds i (Finset.mem_range.mp hi))
  rw [he] at h
  norm_num [point, cap, Finset.sum_range_succ] at h ⊢
  linarith

theorem scalar_uniform {L : ℝ} (hL : 3100 ≤ L) : scalar L ≤ 31 / 100000 := by
  linarith [uniform_reduction hL, fixed_core_paid]

theorem original_source26_scalar {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in Real.log (3.36 * L ^ (3 : ℕ))..Real.log (L ^ (3 : ℕ) * L ^ (15 : ℕ)),
      Real.exp (-s) *
        ((17102 + 254231 / s) * s ^ (6 : ℕ) * L ^ (5 : ℕ) / (L - 4 * s) *
            Real.exp (-0.478 * (L - 4 * s) / s) +
          16541 * s ^ (6 : ℕ) * L ^ (4 : ℕ) * Real.exp (-0.478 * L / s))) ≤
      31 / 100000 :=
  scalar_uniform hL

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate
