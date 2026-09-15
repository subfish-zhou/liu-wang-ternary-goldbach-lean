import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.Source27Payment

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27

def lower (L : ℝ) : ℝ := Real.log (3.36 * L ^ 3)

def upper (L : ℝ) : ℝ := Real.log (10000 * L ^ 3 * Real.log (L ^ 3))

def integrand (L s : ℝ) : ℝ :=
  L ^ 4 *
    (s / Real.pi - 0.874 + (6.8423 / 7) * (1 / 100000) * s * Real.exp (-s) +
      (15 / 7) * (1 / 100000) * Real.exp (-s)) * Real.exp (-0.478 * L / s)

def scalar (L : ℝ) : ℝ := ∫ s in lower L..upper L, integrand L s

theorem integrand_literal (L s : ℝ) :
    integrand L s =
      L ^ 4 *
        (s / Real.pi - 0.874 + (6.8423 / 7) * (1 / 100000) * s * Real.exp (-s) +
          (15 / 7) * (1 / 100000) * Real.exp (-s)) * Real.exp (-0.478 * L / s) := rfl

theorem scalar_literal (L : ℝ) :
    scalar L =
      ∫ s in Real.log (3.36 * L ^ 3)..Real.log (10000 * L ^ 3 * Real.log (L ^ 3)),
        L ^ 4 *
          (s / Real.pi - 0.874 + (6.8423 / 7) * (1 / 100000) * s * Real.exp (-s) +
            (15 / 7) * (1 / 100000) * Real.exp (-s)) * Real.exp (-0.478 * L / s) := rfl

theorem integrand_eq_frozen (L s : ℝ) :
    integrand L s = source27Integrand L s := rfl

theorem scalar_uniform {L : ℝ} (hL : 3100 ≤ L) :
    scalar L ≤ 197 / 100000 := by
  change (∫ s in Real.log (3.36 * L ^ 3)..
    Real.log (10000 * L ^ 3 * Real.log (L ^ 3)), source27Integrand L s) ≤ _
  convert! original_source27_payment hL using 1
  norm_num

theorem original_source27_scalar {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in Real.log (3.36 * L ^ 3)..Real.log (10000 * L ^ 3 * Real.log (L ^ 3)),
      L ^ 4 *
        (s / Real.pi - 0.874 + (6.8423 / 7) * (1 / 100000) * s * Real.exp (-s) +
          (15 / 7) * (1 / 100000) * Real.exp (-s)) * Real.exp (-0.478 * L / s)) ≤
      197 / 100000 :=
  scalar_uniform hL

theorem original_endpoints {L : ℝ} (hL : 3100 ≤ L) :
    10 ≤ lower L ∧ lower L ≤ upper L :=
  source27_original_endpoints hL

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27
