import LiuWang.Proof.Campaign20260915.HighSums.HeightCompensation

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.WeightedHighZeros.Continuation
open LiuWang.Proof.SourceRoute.HighSum

namespace LiuWang.Proof.Campaign20260915.HighSums

def belowHeightLayerCorrection (N q : ℕ) [NeZero q] : ℝ :=
  ∫ alpha in (19 / 20 : ℝ)..1,
    layerKernel N alpha *
      ((belowHeightFamilyCount q alpha (omegaCutoff N q) : ℝ) / omegaCutoff N q)

theorem below_height_layer_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun alpha => layerKernel N alpha *
      ((belowHeightFamilyCount q alpha (omegaCutoff N q) : ℝ) / omegaCutoff N q))
      volume (19 / 20) 1 := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have h1 := (family_alpha_integrable (q := q) hn (sourceT N)).div_const (sourceT N)
  have h2 := family_height_alpha_integrable (q := q) hn hu
    (WeightedLowZeros.omegaCutoff_le_sourceT hN)
  apply ((h1.add h2).sub (source_integrand_integrable (q := q) hn)).congr
  intro alpha _
  dsimp only
  rw [sourceMass_eq_compensated_height hN hq alpha]
  ring

theorem belowHeightLayerCorrection_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    0 ≤ belowHeightLayerCorrection N q := by
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hL : 0 ≤ sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  apply intervalIntegral.integral_nonneg_of_forall (by norm_num : (19 / 20 : ℝ) ≤ 1)
  intro alpha
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL)
    (below_height_correction_nonneg q alpha hu)

theorem excessHighSum_add_belowHeightLayerCorrection {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    excessHighSum N q + belowHeightLayerCorrection N q =
      (∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ∫ alpha in (19 / 20 : ℝ)..1,
          layerKernel N alpha * (familyCount q alpha y : ℝ) := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have h1 := (family_alpha_integrable (q := q) hn (sourceT N)).div_const (sourceT N)
  have h2 := family_height_alpha_integrable (q := q) hn hu
    (WeightedLowZeros.omegaCutoff_le_sourceT hN)
  rw [excessHighSum_eq_source_integral hn, belowHeightLayerCorrection,
    ← original_height_alpha_swap hN hq]
  change (∫ alpha in (19 / 20 : ℝ)..1,
    layerKernel N alpha * sourceMass N q alpha) + _ = _
  rw [← intervalIntegral.integral_add (source_integrand_integrable (q := q) hn)
      (below_height_layer_integrable hN hq),
    ← intervalIntegral.integral_div, ← intervalIntegral.integral_add h1 h2]
  apply intervalIntegral.integral_congr
  intro alpha _
  dsimp only
  rw [sourceMass_eq_compensated_height hN hq alpha]
  ring

#print axioms below_height_layer_integrable
#print axioms excessHighSum_add_belowHeightLayerCorrection

end LiuWang.Proof.Campaign20260915.HighSums
