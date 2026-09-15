import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact headline target, not an assumed theorem

Liu–Wang, Acta Arithmetica 105 (2002), Theorem 1, p.134.
No assertion of this proposition is introduced here. In particular, no
external mathematical axiom or `sorry` supplies it.
-/
namespace LiuWang

/-- Three odd primes, with repetition permitted. -/
def IsThreeOddPrimeSum (N : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
    Odd p ∧ Odd q ∧ Odd r ∧ N = p + q + r

/-- The paper's literal threshold is `exp 3100`, not `10 ^ 3100`.
This is a specification; the foundation library does not prove it. -/
def TheoremStatement : Prop :=
  ∀ N : ℕ, Odd N → Real.exp 3100 ≤ (N : ℝ) → IsThreeOddPrimeSum N

end LiuWang
