import LiuWang.Proof.Campaign20260915.Parent.AllArcsPaid
import LiuWang.Proof.Campaign20260915.Density.FamilyPaid

/-! The original large-odd-N root with the density input discharged.
Three explicit mathematical inputs remain: finite-height zeta verification,
the global totient inequality, and the small-conductor exclusion.
This is not yet an unconditional proof of the original large-N theorem.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.Campaign20260915.Parent.DensityPaidRoot

 theorem threeOddPrimes_of_three_shared_inputs {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hzeta : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      16 < |s.im| → |s.im| < 1894438 → s.re = 1 / 2)
    (htotient : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤
      LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.nu q)
    (hsmall : ∀ (q : ℕ) [NeZero q] (chi : Character q),
      chi.IsPrimitive → chi ≠ 1 → chi ^ 2 = 1 → ∀ x beta : ℝ,
      10 ≤ x → (q : ℝ) ≤ x →
      1 - 1 / (9.645908801 * Real.log x) ≤ beta →
      chi.LFunction (beta : ℂ) = 0 → 987 ≤ q) :
    LiuWang.IsThreeOddPrimeSum N := by
  exact AllArcsPaid.threeOddPrimes_of_four_shared_inputs hN hodd
    (fun q _ => Density.source_T7 q) hzeta htotient hsmall

#print threeOddPrimes_of_three_shared_inputs
#print axioms threeOddPrimes_of_three_shared_inputs
#print axioms LiuWang.Proof.Campaign20260915.Density.strict_nonprincipal_chen_all
#print axioms LiuWang.Proof.Campaign20260915.Density.source_T7
#print axioms LiuWang.Proof.Campaign20260915.Density.complete_family_sourceSeven_paid

end LiuWang.Proof.Campaign20260915.Parent.DensityPaidRoot
