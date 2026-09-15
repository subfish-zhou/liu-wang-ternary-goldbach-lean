import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Certificate

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem source35_height_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    heightEnvelope profile35 N q ≤ 0.0102654 * q / sourceL N ^ 4 := by
  have hh := envelope_log_extension profile35_continuousOn (fun _ _ => profile35_nonneg) hN hq
  have hp := mul_le_mul_of_nonneg_left (scalar35_uniform (Parameters.sourceL_ge_3100 hN))
    (show (0 : ℝ) ≤ (q : ℝ) / sourceL N ^ 4 by positivity)
  change heightEnvelope profile35 N q ≤ (q : ℝ) / sourceL N ^ 4 * scalar35 (sourceL N) at hh
  exact (hh.trans hp).trans_eq (by ring)

theorem source36_height_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    heightEnvelope profile36 N q ≤ 0.0016 * q / sourceL N ^ 4 := by
  have hh := envelope_log_extension profile36_continuousOn (fun _ _ => profile36_nonneg) hN hq
  have hp := mul_le_mul_of_nonneg_left (scalar36_uniform (Parameters.sourceL_ge_3100 hN))
    (show (0 : ℝ) ≤ (q : ℝ) / sourceL N ^ 4 by positivity)
  change heightEnvelope profile36 N q ≤ (q : ℝ) / sourceL N ^ 4 * scalar36 (sourceL N) at hh
  exact (hh.trans hp).trans_eq (by ring)

theorem actual_source35 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), FirstCase q y) :
    finiteK3 N q ≤ 0.0102654 * q / sourceL N ^ 4 :=
  (actual_source35_height hN hq hcase).trans (source35_height_paid hN hq)

theorem actual_source36 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), SecondCase q y) :
    finiteK3 N q ≤ 0.0016 * q / sourceL N ^ 4 :=
  (actual_source36_height hN hq hcase).trans (source36_height_paid hN hq)

theorem actual_source35_with_zero_tail {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), FirstCase q y) :
    (∫ y in omegaCutoff N q..sourceT N, heightKernel y * lambdaCountSegment N q y 0 0.36) ≤
      zeroTail N q + 0.0102654 * q / sourceL N ^ 4 := by
  rw [original_height_zero_tail hN hq]
  exact add_le_add le_rfl (actual_source35 hN hq hcase)

theorem actual_source36_with_zero_tail {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), SecondCase q y) :
    (∫ y in omegaCutoff N q..sourceT N, heightKernel y * lambdaCountSegment N q y 0 0.36) ≤
      zeroTail N q + 0.0016 * q / sourceL N ^ 4 := by
  rw [original_height_zero_tail hN hq]
  exact add_le_add le_rfl (actual_source36 hN hq hcase)

theorem source35_original_height_literal (N q : ℕ) :
    heightEnvelope profile35 N q =
      ∫ y in omegaCutoff N q..sourceT N, (1 / y ^ 2) *
        (2 * Real.exp (-sourceL N / (9.645908801 * Real.log ((q : ℝ) * y))) +
          11 * Real.exp (-0.3221 * sourceL N / Real.log ((q : ℝ) * y)) +
          7 * Real.exp (-0.33 * sourceL N / Real.log ((q : ℝ) * y)) -
          20 * Real.exp (-0.36 * sourceL N / Real.log ((q : ℝ) * y))) := rfl

theorem finiteK3_literal (N q : ℕ) [NeZero q] :
    finiteK3 N q =
      ∫ y in omegaCutoff N q..sourceT N, (1 / y ^ 2) *
        (sourceL N / Real.log ((q : ℝ) * y) *
          ∫ lam in (1 / 9.645908801 : ℝ)..0.36,
            (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y)) *
              (DirichletZeroCount.familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ)) := rfl

theorem source35_height_power {N : ℕ} (hN : 0 < N) (q : ℕ) :
    heightEnvelope profile35 N q =
      ∫ y in omegaCutoff N q..sourceT N, (1 / y ^ 2) *
        (2 * (N : ℝ) ^ (-1 / (9.645908801 * Real.log ((q : ℝ) * y))) +
          11 * (N : ℝ) ^ (-0.3221 / Real.log ((q : ℝ) * y)) +
          7 * (N : ℝ) ^ (-0.33 / Real.log ((q : ℝ) * y)) -
          20 * (N : ℝ) ^ (-0.36 / Real.log ((q : ℝ) * y))) := by
  rw [source35_original_height_literal]
  simp_rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hN)]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  have he (r s : ℝ) : Real.log (N : ℝ) * (-r / s) = -r * sourceL N / s := by
    unfold sourceL
    ring
  simp_rw [he]
  rw [show -(1 : ℝ) * sourceL N = -sourceL N by ring]

theorem zeroTail_literal (N q : ℕ) [NeZero q] :
    zeroTail N q =
      ∫ y in omegaCutoff N q..sourceT N, (1 / y ^ 2) *
        (sourceL N / Real.log ((q : ℝ) * y) *
          ∫ lam in (0 : ℝ)..(1 / 9.645908801),
            (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y)) *
              (DirichletZeroCount.familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ)) := rfl

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
