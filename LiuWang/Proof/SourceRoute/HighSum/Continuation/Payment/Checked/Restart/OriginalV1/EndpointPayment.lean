import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.EndpointComparison
import LiuWang.Proof.SourceRoute.HighSum.SourceReduction

/-! LW (2.21): actual closed-height counts and their alpha integral.

The mathematical input is the original LWD T7 inequality, on its printed
domain. It is not supplied by the frozen low-alpha T7 producer.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1

theorem source21_count_compare {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    {alpha : ℝ} (ha : 19 / 20 ≤ alpha) :
    (familyCount q alpha (sourceT N) : ℝ) ≤
      (17102 + 254231 / (18 * Real.log (sourceL N))) *
        (18 * Real.log (sourceL N)) ^ (57 / 10 : ℝ) *
          sourceL N ^ (69 / 20 : ℝ) +
        16541 * (15 * Real.log (sourceL N)) ^ (6 : ℕ) := by
  have hm : familyCount q alpha (sourceT N) ≤
      familyCount q (19 / 20) (sourceT N) :=
    Finset.sum_le_sum (fun chi _ => count_antitone_alpha chi (sourceT N) ha)
  exact (Nat.cast_le.mpr hm).trans
    ((hT7 (19 / 20) (sourceT N) (by norm_num) (by norm_num)
      (source21_height_domain hN hq)).trans (source21_expression_compare hN hq))

theorem source21_endpoint_integral {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y) :
    (∫ alpha in (19 / 20 : ℝ)..1,
      layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N ≤
      (18 / 100000000000 : ℝ) / sourceL N ^ (4 : ℕ) := by
  let C := (17102 + 254231 / (18 * Real.log (sourceL N))) *
    (18 * Real.log (sourceL N)) ^ (57 / 10 : ℝ) *
      sourceL N ^ (69 / 20 : ℝ) +
    16541 * (15 * Real.log (sourceL N)) ^ (6 : ℕ)
  have hn := Parameters.nat_pos_of_exp_le hN
  have hL := Parameters.sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hlog : 0 < Real.log (sourceL N) := Real.log_pos (by linarith)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hT0 : 0 < sourceT N := by unfold sourceT; positivity
  have hi :
      (∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) ≤ C := by
    calc
      _ ≤ ∫ alpha in (19 / 20 : ℝ)..1, layerKernel N alpha * C := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (family_alpha_integrable hn _)
          (((continuous_layerKernel hn).mul continuous_const).intervalIntegrable _ _)
        intro alpha ha
        exact mul_le_mul_of_nonneg_left (source21_count_compare hN hq hT7 ha.1)
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL0.le)
      _ ≤ C := by
        rw [intervalIntegral.integral_mul_const,
          WeightedHighZeros.Continuation.integral_layerKernel hn]
        norm_num only [sub_self, Real.rpow_zero]
        nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) ((19 / 20 : ℝ) - 1)]
  have he : C / sourceT N =
      (17102 + 254231 / (18 * Real.log (sourceL N))) *
          (18 * Real.log (sourceL N)) ^ (57 / 10 : ℝ) *
          sourceL N ^ ((69 : ℝ) / 20 - 15) +
        16541 / sourceL N ^ (15 : ℕ) *
          (15 * Real.log (sourceL N)) ^ (6 : ℕ) := by
    dsimp only [C, sourceT]
    rw [Real.rpow_sub hL0, Real.rpow_ofNat]
    ring
  exact (div_le_div_of_nonneg_right hi hT0.le).trans
    (he.trans_le (original_source21_scalar hL))

theorem source21_excess_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y) :
    excessHighSum N q ≤ (18 / 100000000000 : ℝ) / sourceL N ^ (4 : ℕ) +
      ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ∫ alpha in (19 / 20 : ℝ)..1,
          layerKernel N alpha * (familyCount q alpha y : ℝ) :=
  (original_excess_le_density_integrals hN hq).trans
    (add_le_add (source21_endpoint_integral hN hq hT7) le_rfl)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
