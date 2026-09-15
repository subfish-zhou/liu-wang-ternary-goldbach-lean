import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Payment
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.Payment

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

inductive Branch
  | first
  | second

def spectralCase (b : Branch) (q : ℕ) [NeZero q] (y : ℝ) : Prop :=
  match b with
  | .first => FirstCase q y
  | .second => SecondCase q y

def branchBudget (b : Branch) : ℝ :=
  match b with
  | .first => 0.0102654
  | .second => 0.0016

theorem finiteK3_paid (b : Branch) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), spectralCase b q y) :
    finiteK3 N q ≤ branchBudget b * q / sourceL N ^ 4 := by
  cases b with
  | first => exact actual_source35 hN hq hcase
  | second => exact actual_source36 hN hq hcase

theorem highSum_large_height (b : Branch) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hlarge : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ omegaCutoff N q)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), spectralCase b q y) :
    highSum N q ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + branchBudget b * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  have hh := Source20.highSum_large_height hN hq hT7 hlarge
  rw [original_height_zero_tail hN hq] at hh
  have hp := finiteK3_paid b hN hq hcase
  linarith

theorem highSum_small_height (b : Branch) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsmall : omegaCutoff N q < max (100000 / (q : ℝ)) (10000 * Real.log q))
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), spectralCase b q y) :
    highSum N q ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (∫ y in omegaCutoff N q..max (100000 / (q : ℝ)) (10000 * Real.log q),
        heightKernel y *
          ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
            layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + branchBudget b * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  have hh := Source20.highSum_small_height hN hq hT7 hsmall
  rw [original_height_zero_tail hN hq] at hh
  have hp := finiteK3_paid b hN hq hcase
  linarith

theorem primedHighSum_large_height (b : Branch) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hlarge : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ omegaCutoff N q)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), spectralCase b q y)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + branchBudget b * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  rw [primedHighSum_eq_highSum hN he]
  exact highSum_large_height b hN hq hT7 hlarge hcase

theorem primedHighSum_small_height (b : Branch) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsmall : omegaCutoff N q < max (100000 / (q : ℝ)) (10000 * Real.log q))
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), spectralCase b q y)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (∫ y in omegaCutoff N q..max (100000 / (q : ℝ)) (10000 * Real.log q),
        heightKernel y *
          ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
            layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + branchBudget b * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  rw [primedHighSum_eq_highSum hN he]
  exact highSum_small_height b hN hq hT7 hsmall hcase

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
