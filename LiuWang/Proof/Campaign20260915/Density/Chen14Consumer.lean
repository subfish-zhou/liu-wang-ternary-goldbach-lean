import LiuWang.Proof.Campaign20260915.Density.Chen14
import LiuWang.Proof.Campaign20260915.Density.Chen24Consumer

set_option autoImplicit false
noncomputable section

open Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem equation_3_45_with_chen14_paid {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    weightedMean y (1 + sourceDelta y) ≤ 90.5727 * Real.log y ^ 5 :=
  MeanBudgets.equation_3_45 hy (fun _ hu => chen14_right_mean hy hu)

theorem equation_3_46_with_chen_inputs_paid {y sigma : ℝ}
    (hy : 10000 * Real.log 6 ≤ y) (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y)) :
    weightedMean y sigma ≤ 90.5727 * Real.exp (4 / 1.5) *
      y ^ (4 * (1 - sigma)) * Real.log y ^ (8 * sigma - 3) :=
  Critical336.equation_3_46_with_zeta_paid hy hs
    (fun _ hu => chen24_mollifier_mean hy hu) (fun _ hu => chen14_right_mean hy hu)

theorem lemma_3_5_with_chen_inputs_paid {y sigma : ℝ}
    (hy : 10000 * Real.log 6 ≤ y) (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y)) :
    M y sigma y ≤ 3318.39 * y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 1) :=
  Critical336.lemma_3_5_with_zeta_paid hy hs
    (fun _ hu => chen24_mollifier_mean hy hu) (fun _ hu => chen14_right_mean hy hu)

theorem lemma_3_5_at_source_shift_with_chen_inputs_paid (q : ℕ) [NeZero q]
    {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + 2 * sourceDelta y ≤ alpha) (ha1 : alpha < 1) :
    M y (alpha - sourceDelta y) y ≤
      3318.39 * y ^ (4 * (1 - (alpha - sourceDelta y))) *
        Real.log y ^ (6 * (alpha - sourceDelta y) - 1) :=
  lemma_3_5_at_source_shift_with_chen24_paid q hy ha ha1
    (fun _ hu => chen14_right_mean (source_height_ge_log_six hy) hu)

#print chen14_right_mean
#print axioms chen14_right_mean
#print axioms equation_3_45_with_chen14_paid
#print axioms equation_3_46_with_chen_inputs_paid
#print axioms lemma_3_5_with_chen_inputs_paid
#print axioms lemma_3_5_at_source_shift_with_chen_inputs_paid

end LiuWang.Proof.Campaign20260915.Density
