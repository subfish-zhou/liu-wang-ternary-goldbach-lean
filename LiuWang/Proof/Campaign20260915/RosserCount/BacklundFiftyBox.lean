import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFiftyPhase
import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalEvaluation

set_option autoImplicit false
set_option maxHeartbeats 3000000

open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundFiftyWeight (n : ℕ) : ℚ := if n = 10 then 1 / 2 else 1

def backlundFiftyRect (n : ℕ) : QComplex × QComplex :=
  let U := backlundFiftyWeight n * reciprocalSqrtUpper n 1000
  ((min 0 ((backlundFiftyPhase n).1 - 13747 / 100000000) * U,
    max 0 ((backlundFiftyPhase n).1 + 13747 / 100000000) * U),
   (min 0 ((backlundFiftyPhase n).2 - 13747 / 100000000) * U,
    max 0 ((backlundFiftyPhase n).2 + 13747 / 100000000) * U))

def backlundFiftyBox : QComplex × QComplex :=
  ((1 + ∑ j ∈ Finset.range 9, (backlundFiftyRect (j + 2)).1.1,
    1 + ∑ j ∈ Finset.range 9, (backlundFiftyRect (j + 2)).1.2),
   (∑ j ∈ Finset.range 9, (backlundFiftyRect (j + 2)).2.1,
    ∑ j ∈ Finset.range 9, (backlundFiftyRect (j + 2)).2.2))

theorem backlundFiftyBox_bounds :
    -(1 : ℚ) ≤ backlundFiftyBox.1.1 ∧ backlundFiftyBox.1.2 ≤ 33 / 20 ∧
      -(1 : ℚ) ≤ backlundFiftyBox.2.1 ∧ backlundFiftyBox.2.2 ≤ 59 / 50 := by
  norm_num [backlundFiftyBox, backlundFiftyRect, backlundFiftyWeight,
    reciprocalSqrtUpper, backlundFiftyPhase, logNaturalCenter, logNaturalRaw,
    roundRational, Nat.log2_eq_log_two, Finset.sum_range_succ]
  norm_num [unitRepeatedSquare, roundQComplex, squareQComplex, unitTaylor,
    realIPower, imagIPower, roundRational, Finset.sum_range_succ]

#print axioms backlundFiftyBox_bounds

end LiuWang.Proof.Campaign20260915.RosserCount
