import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.NormalizedSourceEndpoint

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization

example :
    ‖sourceZetaPolynomialRemainder (1 / 2) 12 12 1‖ ≤
      (371 / 500) * ((12 : ℝ) ^ (-(1 / 2 : ℝ)) / 12) :=
  complete_source_R0_integer (by norm_num) (by norm_num)

example :
    ‖sourceZetaPolynomialRemainder (1 / 2) 45 45 7‖ ≤
      (129 / 125) * ((45 : ℝ) ^ (-(1 / 2 : ℝ)) / 45 ^ 3) :=
  complete_source_R2_integer (by norm_num) (by norm_num)

example {n : ℕ} (ht : 125 < (n : ℝ) ^ 2) :
    |normalizedCriticalZeta (sourceTime n) -
      (sourceRealMainSum (sourceTime n) n + sourcePolynomialNormalized n n 1)| <
        (3 / 4) * ((n : ℝ) ^ 2) ^ (-(3 / 4 : ℝ)) := by
  simpa only [Nat.floor_natCast] using normalized_source_one_strict (Nat.cast_nonneg n) ht

example {n : ℕ} (ht : 2000 < (n : ℝ) ^ 2) :
    |normalizedCriticalZeta (sourceTime n) -
      (sourceRealMainSum (sourceTime n) n + sourcePolynomialNormalized n n 7)| <
        (57 / 50) * ((n : ℝ) ^ 2) ^ (-(7 / 4 : ℝ)) := by
  simpa only [Nat.floor_natCast] using normalized_source_seven_strict (Nat.cast_nonneg n) ht

example : (3 / 4 : ℝ) - 371 / 500 = 1 / 125 ∧
    (57 / 50 : ℝ) - 129 / 125 = 27 / 250 ∧
    (0 : ℝ) < 1 / 125 ∧ (0 : ℝ) < 27 / 250 := by norm_num

#print axioms left_tail_thousandth_scalar
#print axioms right_tail_thousandth_scalar
#print axioms source_error_scale
#print axioms source_error_scale_original
#print axioms left_tail_source_allocation
#print axioms right_tail_source_allocation
#print axioms source_error_scale_three_le_one
#print axioms source_remainder_three_piece_identity
#print axioms source_remainder_three_piece_bound
#print axioms complete_source_R0_noninteger
#print axioms complete_source_R2_noninteger
#print axioms complete_source_R0_integer
#print axioms complete_source_R2_integer
#print axioms complete_source_R0_all
#print axioms complete_source_R2_all
#print axioms complete_source_R0_margin
#print axioms complete_source_R2_margin
#print axioms complete_source_R0_strict
#print axioms complete_source_R2_strict
#print axioms sourcePolynomialNormalized_seven_noninteger
#print axioms normalized_zeta_sourcePolynomial_residual
#print axioms normalized_source_remainder_bound
#print axioms normalized_source_one_margin
#print axioms normalized_source_seven_margin
#print axioms normalized_source_one_strict
#print axioms normalized_source_seven_strict

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
