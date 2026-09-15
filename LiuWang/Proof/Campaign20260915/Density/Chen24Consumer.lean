import LiuWang.Proof.Campaign20260915.Density.Chen24
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.Consumer

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem lemma_3_4_with_chen24_paid {y u : ℝ}
    (hy : 10000 * Real.log 6 ≤ y) (hu : 0 ≤ u) :
    M y (1 / 2) (y * u) ≤
      12.508 * y * (2 + y * u) * (2.19021 * u + 2.906) * Real.log y :=
  Critical336.lemma_3_4_with_zeta_paid hy hu (chen24_mollifier_mean hy hu)

theorem equation_3_44_with_chen24_paid {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    weightedMean y (1 / 2) ≤ 254.13 * y ^ 2 * Real.log y :=
  MeanBudgets.equation_3_44_from_3_36 hy Critical336.equation_3_36
    (fun _ hu => chen24_mollifier_mean hy hu)

theorem lemma_3_5_at_source_shift_with_chen24_paid (q : ℕ) [NeZero q]
    {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + 2 * sourceDelta y ≤ alpha) (ha1 : alpha < 1)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    M y (alpha - sourceDelta y) y ≤
      3318.39 * y ^ (4 * (1 - (alpha - sourceDelta y))) *
        Real.log y ^ (6 * (alpha - sourceDelta y) - 1) :=
  Critical336.lemma_3_5_at_source_shift_with_zeta_paid q hy ha ha1
    (fun _ hu => chen24_mollifier_mean (source_height_ge_log_six hy) hu) hchen14

#print axioms lemma_3_4_with_chen24_paid
#print axioms equation_3_44_with_chen24_paid
#print axioms lemma_3_5_at_source_shift_with_chen24_paid

end LiuWang.Proof.Campaign20260915.Density
