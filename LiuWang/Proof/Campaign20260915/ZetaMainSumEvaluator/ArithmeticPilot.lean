import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.BatchEvaluator

set_option autoImplicit false
set_option maxRecDepth 10000

namespace LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem pilot_cache_exact :
    buildSharedCache 1000 8 4 =
      [⟨0, 141 / 16000, 1000 / 1001, 1 / 1001⟩,
       ⟨173 / 250, 407 / 32000, 200 / 283, 100 / 200081⟩,
       ⟨1097 / 1000, 407 / 32000, 1000 / 1733, 250 / 750389⟩,
       ⟨277 / 200, 133 / 8000, 1000 / 2001, 1 / 4002⟩] := by
  have h1 : Nat.log2 1 = 0 := by decide
  have h3 : Nat.log2 3 = 1 := by decide
  have h4 : Nat.log2 4 = 2 := by decide
  norm_num [buildSharedCache, List.range_succ, logExponent, logOneMinusSeries,
    Finset.sum_range_succ, roundRationalAt, h1, h3, h4]

theorem pilot_negative_rounding : roundRationalAt 10 (-1 / 3) = -2 / 5 := by
  norm_num [roundRationalAt]

theorem pilot_sequential_rounding :
    roundedSum 10 (fun n => if n = 0 then -1 / 3 else 1 / 7) 3 = -1 / 5 := by
  norm_num [roundedSum, roundRationalAt]

theorem pilot_insufficient_cache :
    evaluatePrefix 1000 (buildSharedCache 1000 8 4) ⟨16, 0, 5⟩ = none :=
  evaluatePrefix_insufficient (by simp [buildSharedCache])

theorem pilot_boundary_window : CutoffWindow 6 7 0 1 := by
  norm_num [CutoffWindow, piLower, piUpper, rationalPi20]

theorem pilot_boundary_not_constant : ¬ CutoffWindow 6 7 0 0 := by
  norm_num [CutoffWindow, piLower, piUpper, rationalPi20]

#print axioms pilot_cache_exact
#print axioms pilot_sequential_rounding
#print axioms pilot_boundary_window

end LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator
