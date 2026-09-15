import LiuWang.Proof.Campaign20260915.ZetaValidation.Power16Evaluation

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def zeta16Block (b : ℕ) : QComplex :=
  (∑ j ∈ Finset.range 8, (power16Center (b * 8 + j + 1)).1,
   ∑ j ∈ Finset.range 8, (power16Center (b * 8 + j + 1)).2)

def zeta16TailCenter : QComplex :=
  (-1281 / 2050 * (power16Center 64).1 + 4096 / 1025 * (power16Center 64).2,
   -1281 / 2050 * (power16Center 64).2 - 4096 / 1025 * (power16Center 64).1)

macro "certify_zeta16_block" : tactic =>
  `(tactic| (
    norm_num [zeta16Block, zeta16TailCenter, power16Center, reciprocalSqrtLower,
      power16Phase, logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ]
    norm_num [unitRepeatedSquare, roundQComplex, squareQComplex, unitTaylor,
      realIPower, imagIPower, roundRational, Finset.sum_range_succ]))

#eval (List.range 8).map fun b =>
  (⌊1000 * (zeta16Block b).1⌋, ⌊1000 * (zeta16Block b).2⌋)
#eval (⌊1000 * zeta16TailCenter.1⌋, ⌊1000 * zeta16TailCenter.2⌋)

end LiuWang.Proof.Campaign20260915.ZetaValidation
