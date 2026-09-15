import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.FiniteCertificate
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Residual

/-! # Actual count and highSum consumers of the single fixed numerical certificate

The named numerical hypothesis below remains an explicit unproved input,
not an axiom, a hidden assumption on all L, or a completed payment.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment

theorem original_integral_normalization (N : ℕ) :
    (∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
      sourceL N ^ (4 : ℕ) * Real.exp (-s) * source31Profile (sourceL N) s) =
      ∫ s in lowerHeight (sourceL N)..upperHeight (sourceL N),
        sourceIntegrand (sourceL N) s := by
  unfold lowerHeight upperHeight sourceP sourceT sourceIntegrand
  rw [← pow_add]

theorem actual_source31_le_finite_certificate {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * lambdaCountSegment N q y 0.36 0.478) ≤
      (q : ℝ) / sourceL N ^ (4 : ℕ) *
        (fixedUpper + 1 / 1000000000000000000000000000) := by
  have h := actual_source31 hN hq
  rw [original_integral_normalization] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (uniform_le_finite_certificate (Parameters.sourceL_ge_3100 hN)) (by positivity))

theorem source32_uniform_of_fixed_certificate
    (hcertificate : fixedUpper + 1 / 1000000000000000000000000000 ≤
      368 / 1000000000000000)
    {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in Real.log (3.36 * L ^ (3 : ℕ))..Real.log (L ^ (18 : ℕ)),
      L ^ (4 : ℕ) * Real.exp (-s) * source31Profile L s) ≤
      368 / 1000000000000000 :=
  (uniform_le_finite_certificate hL).trans hcertificate

theorem actual_source32_of_fixed_certificate
    (hcertificate : fixedUpper + 1 / 1000000000000000000000000000 ≤
      368 / 1000000000000000)
    {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * lambdaCountSegment N q y 0.36 0.478) ≤
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  have h := (actual_source31_le_finite_certificate hN hq).trans
    (mul_le_mul_of_nonneg_left hcertificate (by positivity : 0 ≤ (q : ℝ) / sourceL N ^ (4 : ℕ)))
  exact h.trans_eq (by ring)

theorem highSum_le_unpaid_add_source32_of_fixed_certificate
    (hcertificate : fixedUpper + 1 / 1000000000000000000000000000 ≤
      368 / 1000000000000000)
    {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ((∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      (∫ y in omegaCutoff N q..sourceT N, heightKernel y * unpaidAlpha N q y) +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ)) := by
  have h := highSum_le_unpaid_add_source31 hN hq
  rw [original_integral_normalization] at h
  have hp := (uniform_le_finite_certificate (Parameters.sourceL_ge_3100 hN)).trans hcertificate
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (q : ℝ) / sourceL N ^ (4 : ℕ))
  have he : (q : ℝ) / sourceL N ^ (4 : ℕ) * (368 / 1000000000000000) =
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by ring
  rw [he] at hh
  linarith

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment
