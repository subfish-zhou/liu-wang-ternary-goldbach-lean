import LiuWang.Proof.Campaign20260915.HighSums.CompensatedAssembly
import LiuWang.Proof.Campaign20260915.HighSums.TailCompensation

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.WeightedHighZeros
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.Campaign20260915.HighSums

theorem exp_neg_ninety_le : Real.exp (-90) ≤ (1 / 100000 : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (90 : ℝ) (by norm_num) 3
  norm_num at h
  rw [Real.exp_neg]
  exact (inv_le_iff_one_le_mul₀ (Real.exp_pos 90)).mpr (by linarith)

theorem paid_high_budget {L Q : ℝ} (hL : 0 < L) (hQ : 1 ≤ Q) :
    Real.exp (-90) / L ^ 4 + (18 / 100000000000 : ℝ) / L ^ 4 +
      (197 / 100000 : ℝ) * Q / L ^ 4 +
      (31 / 100000 : ℝ) * Q / L ^ 4 + 0.0102654 * Q / L ^ 4 +
      (368 / 1000000000000000 : ℝ) * Q / L ^ 4 ≤ 0.0126 * Q / L ^ 4 := by
  simp only [← add_div]
  apply (div_le_div_iff_of_pos_right (pow_pos hL 4)).mpr
  linarith [exp_neg_ninety_le]

theorem highSum_large_height_of_near_one_real {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hlarge : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ omegaCutoff N q)
    (hreal : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ), rho ∈ zeroValues chi 0 y →
        1 - (1 / c1) / Real.log ((q : ℝ) * y) < rho.re → rho.im = 0) :
    highSum N q ≤ 0.0126 * q / sourceL N ^ 4 := by
  have hh := compensated_highSum_large_height hN hq hT1 hT7 hlarge
  have ht := zeroTail_le_compensation_of_near_one_real hN hq hreal
  have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hb := paid_high_budget hL hQ
  have hs : 0 ≤ (197 / 100000 : ℝ) * q / sourceL N ^ 4 := by positivity
  linarith

theorem highSum_small_height_of_near_one_real {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsmall : omegaCutoff N q < Source27.q1 q)
    (hreal : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ), rho ∈ zeroValues chi 0 y →
        1 - (1 / c1) / Real.log ((q : ℝ) * y) < rho.re → rho.im = 0) :
    highSum N q ≤ 0.0126 * q / sourceL N ^ 4 +
      (q : ℝ) / sourceL N ^ 4 *
        Source27.transferRemainder (sourceL N) q q.totient
          (Real.log ((q : ℝ) * Source27.q1 q)) := by
  have hh := compensated_highSum_small_height hN hq hT1 hT7 hsmall
  have ht := zeroTail_le_compensation_of_near_one_real hN hq hreal
  have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hb := paid_high_budget hL hQ
  linarith

#print axioms paid_high_budget
#print axioms highSum_large_height_of_near_one_real
#print axioms highSum_small_height_of_near_one_real

end LiuWang.Proof.Campaign20260915.HighSums
