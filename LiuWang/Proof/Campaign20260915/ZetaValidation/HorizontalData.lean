import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16BlockData

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def horizontalCoefficient (j : ℕ) : ℚ :=
  (([999, 66, 170, -492, 364, -377, 363, -100,
    -276, 206, 236, -136, -272, -50, 205, 232,
    53, -151, -230, -155, 3, 147, 207, 170,
    65, -57, -151, -189, -166, -97, -7, 80,
    143, 170, 159, 117, 55, -14, -77, -125,
    -151, -154, -135, -99, -52, -1, 48, 90,
    120, 137, 139, 128, 105, 74, 37, -1,
    -38, -71, -97, -116, -126, -127, -120, -106] : List ℚ).getD j 0 - 1) / 1000

macro "certify_horizontal_coefficient" : tactic =>
  `(tactic| (
    norm_num [horizontalCoefficient, power16Center, reciprocalSqrtLower,
      power16Phase, logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ]
    norm_num [unitRepeatedSquare, roundQComplex, squareQComplex, unitTaylor,
      realIPower, imagIPower, roundRational, Finset.sum_range_succ]))

end LiuWang.Proof.Campaign20260915.ZetaValidation
