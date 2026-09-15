import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27.Normalization

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27

def differenceKernel (L Q phi s : ℝ) : ℝ :=
  L ^ 4 *
      ((phi / Q - 1) * (s / Real.pi - 0.874) +
        (phi - 1 / 700000) * (6.8423 * s + 15) * Real.exp (-s)) *
      Real.exp (-0.478 * L / s) -
    L ^ 4 * (phi / Q * (s / Real.pi - 0.874) +
      phi * (6.8423 * s + 15) * Real.exp (-s)) * Real.exp (-L / 20)

def transferRemainder (L Q phi t : ℝ) : ℝ :=
  (∫ s in lower L..t, differenceKernel L Q phi s) -
    ∫ s in t..upper L, integrand L s

theorem integrand_grouped (L s : ℝ) :
    integrand L s =
      L ^ 4 * (s / Real.pi - 0.874 +
        (1 / 700000) * (6.8423 * s + 15) * Real.exp (-s)) *
          Real.exp (-0.478 * L / s) := by
  unfold integrand
  ring

theorem normalizedKernel_eq_literal_add_difference (L Q phi s : ℝ) :
    normalizedKernel L Q phi s = integrand L s + differenceKernel L Q phi s := by
  rw [integrand_grouped]
  unfold normalizedKernel differenceKernel
  ring

theorem integrand_integrable (L : ℝ) {a b : ℝ} (ha : 10 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (integrand L) volume a b := by
  have hs : ∀ s ∈ Set.uIcc a b, s ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    linarith [hs.1]
  apply ContinuousOn.intervalIntegrable
  unfold integrand
  fun_prop

theorem normalizedKernel_integrable (L Q phi : ℝ) {a b : ℝ}
    (ha : 10 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (normalizedKernel L Q phi) volume a b := by
  have hs : ∀ s ∈ Set.uIcc a b, s ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    linarith [hs.1]
  apply ContinuousOn.intervalIntegrable
  unfold normalizedKernel
  fun_prop

theorem differenceKernel_integrable (L Q phi : ℝ) {a b : ℝ}
    (ha : 10 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (differenceKernel L Q phi) volume a b := by
  apply ((normalizedKernel_integrable L Q phi ha hab).sub
    (integrand_integrable L ha hab)).congr
  intro s _
  dsimp only
  linarith [normalizedKernel_eq_literal_add_difference L Q phi s]

theorem cutEnvelope_eq_literal_add_remainder {L t : ℝ} (hL : 3100 ≤ L)
    (ht : lower L ≤ t) (htu : t ≤ upper L) (Q phi : ℝ) :
    (∫ s in lower L..t, normalizedKernel L Q phi s) =
      scalar L + transferRemainder L Q phi t := by
  have ha := (original_endpoints hL).1
  have hi := integrand_integrable L ha ht
  have hj := integrand_integrable L (ha.trans ht) htu
  have hd := differenceKernel_integrable L Q phi ha ht
  have hs := intervalIntegral.integral_add_adjacent_intervals hi hj
  have he : (∫ s in lower L..t, normalizedKernel L Q phi s) =
      (∫ s in lower L..t, integrand L s) +
        ∫ s in lower L..t, differenceKernel L Q phi s := by
    simp_rw [normalizedKernel_eq_literal_add_difference]
    exact intervalIntegral.integral_add hi hd
  unfold scalar transferRemainder
  linarith

theorem exactEnvelope_eq_literal_add_remainder {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : omegaCutoff N q < q1 q) :
    exactEnvelope N q = scalar (sourceL N) +
      transferRemainder (sourceL N) q q.totient (Real.log ((q : ℝ) * q1 q)) := by
  have hd := short_domain hN hq hshort
  exact cutEnvelope_eq_literal_add_remainder (Parameters.sourceL_ge_3100 hN)
    hd.2.2.2.1 hd.2.2.2.2 q q.totient

theorem heightEnvelope_eq_literal_add_remainder {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : omegaCutoff N q < q1 q) :
    heightEnvelope N q = (q : ℝ) / sourceL N ^ 4 *
      (scalar (sourceL N) +
        transferRemainder (sourceL N) q q.totient (Real.log ((q : ℝ) * q1 q))) := by
  rw [heightEnvelope_eq_exact hN hq hshort, exactEnvelope_eq_literal_add_remainder hN hq hshort]

theorem actualShort_le_literal_add_remainder {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : omegaCutoff N q < q1 q) :
    actualShort N q ≤ (q : ℝ) / sourceL N ^ 4 *
      (scalar (sourceL N) +
        transferRemainder (sourceL N) q q.totient (Real.log ((q : ℝ) * q1 q))) := by
  rw [← heightEnvelope_eq_literal_add_remainder hN hq hshort]
  exact actualShort_le_heightEnvelope hN hq hshort

theorem phi_coefficient_directions (q : ℕ) [NeZero q] :
    (q.totient : ℝ) / q ≤ 1 ∧ (1 / 700000 : ℝ) < q.totient := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hp : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  exact ⟨(div_le_one hq).mpr (Nat.cast_le.mpr (Nat.totient_le q)), by linarith⟩

theorem small_height_reciprocal_direction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : omegaCutoff N q < q1 q) :
    1 / (q : ℝ) ≤ (1 / 700000 : ℝ) ∧
      (1 / 700000 : ℝ) < q.totient := by
  have hg : (700000 : ℝ) ≤ q := by exact_mod_cast (short_domain hN hq hshort).1
  exact ⟨one_div_le_one_div_of_le (by norm_num) hg, (phi_coefficient_directions q).2⟩

theorem main_coefficient_difference_nonpos (q : ℕ) [NeZero q] {s : ℝ} (hs : 10 ≤ s) :
    ((q.totient : ℝ) / q - 1) * (s / Real.pi - 0.874) ≤ 0 := by
  have hb : 0.874 ≤ s / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_four]
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (phi_coefficient_directions q).1) (sub_nonneg.mpr hb)

theorem exp_coefficient_difference_pos (q : ℕ) [NeZero q] {s : ℝ} (hs : 10 ≤ s) :
    ((q.totient : ℝ) - 1 / 700000) * (6.8423 * s + 15) * Real.exp (-s) > 0 := by
  have hp := (phi_coefficient_directions q).2
  exact mul_pos (mul_pos (sub_pos.mpr hp) (by linarith)) (Real.exp_pos _)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27
