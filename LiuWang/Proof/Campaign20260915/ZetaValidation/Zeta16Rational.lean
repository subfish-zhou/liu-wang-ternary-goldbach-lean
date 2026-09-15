import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Block0
import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Block1
import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Block2
import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Block3
import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Block4
import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Block5
import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Block6
import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Block7

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def zeta16Center : QComplex :=
  ((∑ j ∈ Finset.range 64, (power16Center (j + 1)).1) -
      1281 / 2050 * (power16Center 64).1 + 4096 / 1025 * (power16Center 64).2,
   (∑ j ∈ Finset.range 64, (power16Center (j + 1)).2) -
      1281 / 2050 * (power16Center 64).2 - 4096 / 1025 * (power16Center 64).1)

theorem zeta16Center_blocks :
    zeta16Center =
      ((∑ b ∈ Finset.range 8, (zeta16Block b).1) + zeta16TailCenter.1,
       (∑ b ∈ Finset.range 8, (zeta16Block b).2) + zeta16TailCenter.2) := by
  apply Prod.ext
  all_goals
    norm_num only [zeta16Center, zeta16Block, zeta16TailCenter,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul]
    ring

theorem zeta16Center_rational_lower :
    (1 / 4 : ℚ) ≤ zeta16Center.1 ∧ (1 / 4 : ℚ) ≤ zeta16Center.2 := by
  rw [zeta16Center_blocks]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 := zeta16Block0_lower
  have h1 := zeta16Block1_lower
  have h2 := zeta16Block2_lower
  have h3 := zeta16Block3_lower
  have h4 := zeta16Block4_lower
  have h5 := zeta16Block5_lower
  have h6 := zeta16Block6_lower
  have h7 := zeta16Block7_lower
  have ht := zeta16TailCenter_lower
  constructor
  · linarith [h0.1, h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1, ht.1]
  · linarith [h0.2, h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2, ht.2]

#print axioms zeta16Center_rational_lower

end LiuWang.Proof.Campaign20260915.ZetaValidation
