import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27.Literal
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.LogSmallHeight
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.EndpointComparison

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27

def q1 (q : ℕ) : ℝ := max (100000 / (q : ℝ)) (10000 * Real.log q)

def actualShort (N q : ℕ) [NeZero q] : ℝ :=
  ∫ y in omegaCutoff N q..q1 q, heightKernel y *
    ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * (familyCount q alpha y : ℝ)

def heightEnvelope (N q : ℕ) : ℝ :=
  ∫ y in omegaCutoff N q..q1 q,
    heightKernel y * ((q.totient : ℝ) * source25Bound q y) *
      (Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) -
        Real.exp (-sourceL N / 20))

def normalizedKernel (L Q phi s : ℝ) : ℝ :=
  L ^ 4 * (phi / Q * (s / Real.pi - 0.874) +
    phi * (6.8423 * s + 15) * Real.exp (-s)) *
      (Real.exp (-0.478 * L / s) - Real.exp (-L / 20))

def exactEnvelope (N q : ℕ) : ℝ :=
  ∫ s in lower (sourceL N)..Real.log ((q : ℝ) * q1 q),
    normalizedKernel (sourceL N) q q.totient s

theorem actualShort_literal (N q : ℕ) [NeZero q] :
    actualShort N q =
      ∫ y in omegaCutoff N q..max (100000 / (q : ℝ)) (10000 * Real.log q),
        (1 / y ^ 2) *
          ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
            (N : ℝ) ^ (alpha - 1) * sourceL N * (familyCount q alpha y : ℝ) := rfl

theorem heightEnvelope_literal (N q : ℕ) :
    heightEnvelope N q =
      ∫ y in omegaCutoff N q..max (100000 / (q : ℝ)) (10000 * Real.log q),
        (1 / y ^ 2) * ((q.totient : ℝ) *
          (y / Real.pi * Real.log ((q : ℝ) * y) - 0.874 * y +
            6.8423 * Real.log ((q : ℝ) * y) + 15)) *
          (Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) -
            Real.exp (-sourceL N / 20)) := rfl

theorem normalizedKernel_factor (L Q phi s : ℝ) (hQ : Q ≠ 0) :
    normalizedKernel L Q phi s =
      L ^ 4 * (phi / Q) * source25LogKernel L Q s := by
  unfold normalizedKernel source25LogKernel
  field_simp

theorem normalizedKernel_cancel {L Q : ℝ} (hL : L ≠ 0) (hQ : Q ≠ 0) (phi s : ℝ) :
    Q / L ^ 4 * normalizedKernel L Q phi s = phi * source25LogKernel L Q s := by
  rw [normalizedKernel_factor _ _ _ _ hQ]
  field_simp

theorem short_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : omegaCutoff N q < q1 q) :
    700000 ≤ q ∧ q1 q = 10000 * Real.log q ∧ q1 q ≤ sourceT N ∧
      lower (sourceL N) ≤ Real.log ((q : ℝ) * q1 q) ∧
      Real.log ((q : ℝ) * q1 q) ≤ upper (sourceL N) := by
  have hg := small_height_gate hN hshort.le (le_refl (q1 q))
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hlog := Real.log_le_log
    (mul_pos (Nat.cast_pos.mpr (NeZero.pos q)) hu)
    (mul_le_mul_of_nonneg_left hshort.le (Nat.cast_nonneg q))
  rw [(original_log_height_bounds hN hq).1] at hlog
  exact ⟨hg.1, hg.2, source21_height_domain hN hq, hlog,
    small_height_log_upper hN hq hshort.le le_rfl⟩

theorem actualShort_le_heightEnvelope {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : omegaCutoff N q < q1 q) :
    actualShort N q ≤ heightEnvelope N q :=
  actual_source25_outer_signed hN hq hshort.le (source21_height_domain hN hq)

theorem heightEnvelope_eq_exact {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : omegaCutoff N q < q1 q) :
    heightEnvelope N q = (q : ℝ) / sourceL N ^ 4 * exactEnvelope N q := by
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hp := original_product_ge (q := q) hN le_rfl
  have hL : sourceL N ≠ 0 := by linarith [Parameters.sourceL_ge_3100 hN]
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  unfold heightEnvelope
  rw [source25_log_substitution hu hshort.le (by linarith),
    (original_log_height_bounds hN hq).1]
  change (q.totient : ℝ) *
    (∫ s in lower (sourceL N)..Real.log ((q : ℝ) * q1 q),
      source25LogKernel (sourceL N) q s) = _
  unfold exactEnvelope
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  exact (normalizedKernel_cancel hL hq0 q.totient s).symm

theorem actualShort_le_exact {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : omegaCutoff N q < q1 q) :
    actualShort N q ≤ (q : ℝ) / sourceL N ^ 4 * exactEnvelope N q := by
  rw [← heightEnvelope_eq_exact hN hq hshort]
  exact actualShort_le_heightEnvelope hN hq hshort

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27
