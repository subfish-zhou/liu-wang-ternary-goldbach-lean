import LiuWang.Proof.Campaign20260915.Totient.NuArithmetic
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1.TotientTail
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ScalarDomain

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Totient

theorem second_sourceNu_eq_nu (x : ℝ) :
    LiuWang.Proof.SourceRoute.SecondArc.Continuation.sourceNu x = nu x := rfl

theorem totient_ratio_le_nu_cutoff_of_RS {P : ℝ} {q : ℕ}
    (hP : 3 ≤ P) (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ P)
    (hRS : ∀ n : ℕ, 3 ≤ n → (n : ℝ) / (n.totient : ℝ) ≤ nu n) :
    (q : ℝ) / (q.totient : ℝ) ≤ nu P := by
  by_cases hq27 : q < 27
  · exact (totient_ratio_le_three_of_lt_27 hq hq27).trans (three_le_nu hP)
  · exact totient_ratio_le_nu_cutoff (by omega) hqP hRS

theorem second_arc_totient_input_of_RS {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hRS : ∀ n : ℕ, 3 ≤ n → (n : ℝ) / (n.totient : ℝ) ≤ nu n) :
    (q : ℝ) / (q.totient : ℝ) ≤
      LiuWang.Proof.SourceRoute.SecondArc.Continuation.sourceNu (sourceP N) :=
  totient_ratio_le_nu_cutoff_of_RS
    (by linarith [sourceP_ge_ten_billion hN]) (NeZero.pos q) hq hRS

theorem second_arc_small_totient_input {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : q < 27) :
    (q : ℝ) / (q.totient : ℝ) ≤
      LiuWang.Proof.SourceRoute.SecondArc.Continuation.sourceNu (sourceP N) :=
  (totient_ratio_le_three_of_lt_27 (NeZero.pos q) hq).trans
    (three_le_nu (by linarith [sourceP_ge_ten_billion hN]))

end LiuWang.Proof.Campaign20260915.Totient
