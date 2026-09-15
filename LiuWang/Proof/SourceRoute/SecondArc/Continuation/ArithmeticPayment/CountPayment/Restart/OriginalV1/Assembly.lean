import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Endpoint
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral.FiniteExpression

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

theorem actual_density_height_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
      ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) =
    (∫ y in (omegaCutoff N q)..densityGate q, heightKernel y *
      ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) +
    (∫ y in densityGate q..middleUpper N q, heightKernel y *
      ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) := by
  have hh := middle_height_domain hN hq
  have hv := densityGate_le_middle hN hq
  have hi := actual_high_alpha_height_integrable hN hq
  apply (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
  · apply hi.mono_set
    rw [Set.uIcc_of_le hgate, Set.uIcc_of_le hh.2.1]
    exact Set.Icc_subset_Icc le_rfl hv
  · apply hi.mono_set
    rw [Set.uIcc_of_le hv, Set.uIcc_of_le hh.2.1]
    exact Set.Icc_subset_Icc hgate le_rfl

theorem actual_high_branch_le_fixed_partition {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N))
    (n : ℕ) (p m : ℕ → ℝ)
    (hp : MonotoneOn p (Set.Icc 0 n))
    (ha : p 0 = lowerLog 3100) (hb : p n = upperLog 3100)
    (hm : ∀ i < n, m i ∈ Set.Icc (p i) (p (i + 1))) :
    (8 * Real.sqrt q / q.totient) *
      (∫ y in max (omegaCutoff N q) (densityGate q)..middleUpper N q, heightKernel y *
        ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      ((8 * Real.exp (4 * 0.478) * sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) *
        ∑ i ∈ Finset.range n,
          FixedIntegral.cellValue ((3100 : ℝ) + Real.log 0.001) (p i) (p (i + 1)) (m i)) /
        sourceL N := by
  have hh := middle_height_domain hN hq
  have hg := densityGate_le_middle hN hq
  exact (actual_high_alpha_height_le_original hN hq (le_max_left _ _)
    (max_le hh.2.1 hg) (le_max_right _ _) hseven hnu).trans
      (div_le_div_of_nonneg_right
        (FixedIntegral.original_all_L_partition_bound (sourceL_ge_3100 hN) n p m hp ha hb hm)
        (by linarith [sourceL_ge_3100 hN]))

theorem actual_two_strips_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
      ∫ alpha in stripLower q y..siegelCutoff q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) =
      actualStripIntegral N q +
      (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
        ∫ alpha in stripUpper q y..siegelCutoff q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) := by
  have hh := middle_height_domain hN hq
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have ho (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    sparse_cutoff_order (middle_log_domain hN hq hy).2.1
  have hi := moving_count_strip_integrable (q := q) hx hh.2.1
    (strip_bounds_continuous hN hq).2 (siegelCutoff_continuous hN hq)
    (fun y hy => (ho y hy).1) (fun y hy => (ho y hy).2.1)
  have hk : ContinuousOn heightKernel (Set.uIcc (omegaCutoff N q) (middleUpper N q)) := by
    rw [Set.uIcc_of_le hh.2.1]
    exact continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (hh.1.trans_le hy.1)))
  have hlast := hi.mul_continuousOn hk
  unfold actualStripIntegral
  rw [← intervalIntegral.integral_add (actualStrip_integrable hN hq)
    (by simpa only [mul_comm] using hlast)]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hh.2.1] at hy
  dsimp only
  rw [← mul_add]
  congr 1
  exact (intervalIntegral.integral_add_adjacent_intervals
    (count_alpha_integrable (q := q) hx (strip_order (q := q) (middle_log_domain hN hq hy).1) y)
    (count_alpha_integrable (q := q) hx (ho y hy).2.1 y)).symm

theorem actual_two_strips_log_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (htwo : ∀ x : ℝ, 8000000000 ≤ x → (q : ℝ) ≤ x →
      ∀ alpha : ℝ, 1 - 0.2067 / Real.log x < alpha → alpha < 1 →
        (familyCount q alpha (x / q) : ℝ) ≤ 2) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) *
      (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
        ∫ alpha in stripLower q y..siegelCutoff q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      (112000 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        (∫ z in lowerLog (sourceL N)..upperLog (sourceL N),
          Real.exp (-z / 2) *
            (Real.exp (-0.2067 * (sourceL N + Real.log 0.001) / z) -
              Real.exp (-0.478 * (sourceL N + Real.log 0.001) / z))) +
      (16 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        (∫ z in lowerLog (sourceL N)..upperLog (sourceL N),
          Real.exp (-z / 2) *
            (Real.exp (-((1 : ℝ) / 9.645908801) * (sourceL N + Real.log 0.001) / z) -
              Real.exp (-0.2067 * (sourceL N + Real.log 0.001) / z))) := by
  rw [actual_two_strips_split hN hq, mul_add]
  exact add_le_add (actual_contribution_516_le hN hq) (actual_last_strip_log_bound hN hq htwo)

theorem endpointDensityBound_source_form {N q : ℕ} [NeZero q] :
    endpointDensityBound q (middleUpper N q) =
      (254231 / Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) + 17102) *
        ((10 * Real.pi * sourceL N ^ (7 : ℕ)) ^ (4 : ℕ) / q) ^ (1 / 60 : ℝ) *
        Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) ^ (6 : ℕ) +
      16541 * Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) ^ (6 : ℕ) := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hp : (q : ℝ) ^ (3 : ℕ) * middleUpper N q ^ (4 : ℕ) =
      (10 * Real.pi * sourceL N ^ (7 : ℕ)) ^ (4 : ℕ) / q := by
    unfold middleUpper
    field_simp
  unfold endpointDensityBound
  rw [hp, (source_log_endpoints (N := N) (q := q)).2]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
