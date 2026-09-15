import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.QBoundary
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh.Consumer

set_option autoImplicit false
noncomputable section

open Complex Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

theorem equation_3_40 {y sigma t : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) 1) :
    ‖Q y ((sigma : ℂ) + t * I)‖ ≤
      (1.3071 * Real.sqrt y) ^ (2 * (1 - sigma)) *
        (1.19 * Real.log y) ^ (2 * sigma - 1) :=
  Titchmarsh.equation_3_40 hs (norm_Q_half hy) (norm_Q_one hy)

theorem equation_3_41 {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y)) :
    M y sigma 1 ≤
      2 * 4.255 * y ^ (2 * (1 - sigma)) * (Real.log y) ^ (4 * sigma) :=
  Titchmarsh.equation_3_41 hy hs (norm_Q_half hy) (norm_Q_one hy)

theorem equation_3_41_at_source_shift (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + 2 * sourceDelta y ≤ alpha) (ha1 : alpha < 1) :
    M y (alpha - sourceDelta y) 1 ≤
      2 * 4.255 * y ^ (2 * (1 - (alpha - sourceDelta y))) *
        (Real.log y) ^ (4 * (alpha - sourceDelta y)) := by
  have hy' := source_height_ge_log_six hy
  exact Titchmarsh.equation_3_41_at_source_shift q hy ha ha1
    (norm_Q_half hy') (norm_Q_one hy')

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic
