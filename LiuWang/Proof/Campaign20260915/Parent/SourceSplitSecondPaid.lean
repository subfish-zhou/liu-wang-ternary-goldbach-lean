import LiuWang.Proof.Campaign20260915.OriginalRegion.BoundaryAudit
import LiuWang.Proof.Campaign20260915.SecondTerminal.ArcTerminal
import LiuWang.Proof.Campaign20260915.Parent.ZetaCompleteAudit

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException.Continuation
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.SecondArc.Continuation

namespace LiuWang.Proof.Campaign20260915.Parent.SourceSplitSecondPaid

theorem threeOddPrimes_of_shared_inputs_and_third {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (h987 : ∀ d e, PaperSource N d e → 987 ≤ (d.modulus : ℝ))
    (hphi : ∀ d e, PaperSource N d e →
      (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hRS : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      16 < |s.im| → |s.im| < 1894438 → s.re = 1 / 2)
    (hT7 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ alpha y : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      (q : ℝ) / q.totient ≤ sourceNu (sourceP N))
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) * ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.IsThreeOddPrimeSum N := by
  have hrs := ZetaCompleteAudit.original_verification_iff_above_sixteen.mpr hRS
  exact OriginalRegion.threeOddPrimes_strict_source_split hN hodd h987 hphi
    (fun q _ hq => SecondTerminal.original_high_T1_input (q := q) hN hq hrs) hT7
    (SecondTerminal.M2_integral_original_4012 hN hrs
      (fun q _ hq y hy alpha h0 h1 => hT7 q hq alpha y h0 h1 hy) hnu) hthird

#print axioms threeOddPrimes_of_shared_inputs_and_third
end LiuWang.Proof.Campaign20260915.Parent.SourceSplitSecondPaid
