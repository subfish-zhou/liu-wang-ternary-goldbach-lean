import LiuWang.Proof.SourceRoute.HighSum.HeightAlpha
import LiuWang.Proof.WeightedLowZeros.Consumer

/-! # Same-q, original-domain reduction to the two density integrals

The imported low-zero module is used only for its parameter comparison
`omegaCutoff_le_sourceT`; no low-zero estimate is repeated or claimed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum

theorem sourceMass_le_full_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (alpha : ℝ) :
    sourceMass N q alpha ≤
      (familyCount q alpha (sourceT N) : ℝ) / sourceT N +
        ∫ y in omegaCutoff N q..sourceT N,
          heightKernel y * (familyCount q alpha y : ℝ) :=
  family_reciprocal_le_height_integral q alpha
    (by linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq])
    (WeightedLowZeros.omegaCutoff_le_sourceT hN)

theorem original_height_alpha_swap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in (19 / 20 : ℝ)..1, layerKernel N alpha *
      ∫ y in omegaCutoff N q..sourceT N,
        heightKernel y * (familyCount q alpha y : ℝ)) =
    ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
      ∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha y : ℝ) :=
  family_height_alpha_swap (Parameters.nat_pos_of_exp_le hN)
    (by linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq])
    (WeightedLowZeros.omegaCutoff_le_sourceT hN)

theorem original_excess_le_density_integrals {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    excessHighSum N q ≤
      (∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ∫ alpha in (19 / 20 : ℝ)..1,
          layerKernel N alpha * (familyCount q alpha y : ℝ) := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have hfirst := (family_alpha_integrable (q := q) hn (sourceT N)).div_const (sourceT N)
  have hsecond := family_height_alpha_integrable (q := q) hn hu huT
  have hi := hfirst.add hsecond
  rw [excessHighSum_eq_source_integral hn, ← original_height_alpha_swap hN hq]
  calc
    _ ≤ ∫ alpha in (19 / 20 : ℝ)..1,
        (layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ) / sourceT N +
          layerKernel N alpha * ∫ y in omegaCutoff N q..sourceT N,
            heightKernel y * (familyCount q alpha y : ℝ)) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (source_integrand_integrable hn) hi
      intro alpha _
      have hk : 0 ≤ layerKernel N alpha := by
        unfold layerKernel
        exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Parameters.sourceL_ge_3100 hN |>.trans' (by norm_num))
      change layerKernel N alpha * sourceMass N q alpha ≤ _
      simpa only [mul_add, mul_div_assoc] using
        mul_le_mul_of_nonneg_left (sourceMass_le_full_height hN hq alpha) hk
    _ = _ := by
      rw [intervalIntegral.integral_add hfirst hsecond, intervalIntegral.integral_div]

theorem original_highSum_le_density_integrals {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ((∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ∫ alpha in (19 / 20 : ℝ)..1,
          layerKernel N alpha * (familyCount q alpha y : ℝ)) :=
  (original_threshold_reduction hN hq).trans
    (add_le_add le_rfl (original_excess_le_density_integrals hN hq))

theorem original_primed_le_density_integrals {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ((∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ∫ alpha in (19 / 20 : ℝ)..1,
          layerKernel N alpha * (familyCount q alpha y : ℝ)) := by
  rw [primedHighSum_eq_highSum hN he]
  exact original_highSum_le_density_integrals hN hq

theorem original_highPacket_le_density_integrals {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : |eta| ≤ deltaRadius N q) :
    ‖highPacket N q a eta‖ ≤ (5 * (N : ℝ) * Real.sqrt q / q.totient) *
      (Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ((∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ∫ alpha in (19 / 20 : ℝ)..1,
          layerKernel N alpha * (familyCount q alpha y : ℝ))) :=
  (highPacket_le_weighted hN ha heta).trans
    (mul_le_mul_of_nonneg_left (original_highSum_le_density_integrals hN hq) (by positivity))

end LiuWang.Proof.SourceRoute.HighSum
