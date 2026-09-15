import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases.Payment
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.Payment

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.WeightedHighZeros LiuWang.Proof.WeightedHighZeros.Continuation
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases

theorem highSum_large_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hlarge : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ omegaCutoff N q) :
    highSum N q ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + 0.0102654 * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  have hh := Source20.highSum_large_height hN hq hT7 hlarge
  rw [original_height_zero_tail hN hq] at hh
  have hp := finiteK3_paid hN hq hT1
  linarith

theorem highSum_small_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsmall : omegaCutoff N q < max (100000 / (q : ℝ)) (10000 * Real.log q)) :
    highSum N q ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (∫ y in omegaCutoff N q..max (100000 / (q : ℝ)) (10000 * Real.log q),
        heightKernel y *
          ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
            layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + 0.0102654 * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  have hh := Source20.highSum_small_height hN hq hT7 hsmall
  rw [original_height_zero_tail hN hq] at hh
  have hp := finiteK3_paid hN hq hT1
  linarith

theorem primedHighSum_large_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hlarge : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ omegaCutoff N q)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + 0.0102654 * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  rw [primedHighSum_eq_highSum hN he]
  exact highSum_large_height hN hq hT1 hT7 hlarge

theorem primedHighSum_small_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsmall : omegaCutoff N q < max (100000 / (q : ℝ)) (10000 * Real.log q))
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (∫ y in omegaCutoff N q..max (100000 / (q : ℝ)) (10000 * Real.log q),
        heightKernel y *
          ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
            layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + 0.0102654 * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  rw [primedHighSum_eq_highSum hN he]
  exact highSum_small_height hN hq hT1 hT7 hsmall

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases
