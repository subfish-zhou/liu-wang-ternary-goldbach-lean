import LiuWang.Foundations.FiniteCircle
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.Main
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.ZeroFreeData
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.FaithfulChoice
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.Multiplicity
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLFunctionOrder
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.Main
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Liu–Wang public interface layer

This module freezes the first shared objects and proof exports used by the
Liu–Wang project without introducing a new omnibus record. Definitions track
the literal source formulas for the finite window, circle-method sums and arcs,
while Dirichlet-character, exceptional-zero and explicit-formula contracts are
re-exported from actual producers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators Interval

namespace LiuWang.Proof.Interfaces

open AnalyticNumberTheory.LargeSieve
open BombieriVinogradov.SiegelWalfisz

/-- The ambient complex Dirichlet-character type used throughout the interface. -/
abbrev Character (q : Nat) := DirichletCharacter Complex q

/-- The exact finite lower endpoint `0.001 N = N / 1000`. -/
def sourceWindowLower (N : Nat) : Real :=
  (N : Real) / 1000

/-- The finite natural window shared with `LiuWang.Fourier.liuWangSupport`. -/
def windowSet (N : Nat) : Set Nat :=
  {n | n ≤ N ∧ N ≤ 1000 * n}

/-- The exact finite support from the existing circle-method producer. -/
abbrev windowFinset (N : Nat) : Finset Nat :=
  LiuWang.Fourier.liuWangSupport N

@[simp] theorem mem_windowSet_iff (N n : Nat) :
    n ∈ windowSet N ↔ n ≤ N ∧ N ≤ 1000 * n :=
  Iff.rfl

@[simp] theorem mem_windowFinset_iff (N n : Nat) :
    n ∈ windowFinset N ↔ n ∈ windowSet N := by
  simp [windowSet, windowFinset, LiuWang.Fourier.mem_liuWangSupport]

/-- The source `L = log N`. -/
def sourceL (N : Nat) : Real :=
  Real.log N

/-- The source `P = L^3`. -/
def sourceP (N : Nat) : Real :=
  sourceL N ^ (3 : Nat)

/-- The source `P1 = L^6`. -/
def sourceP1 (N : Nat) : Real :=
  sourceL N ^ (6 : Nat)

/-- The source `Q = N L^{-7}`. -/
def sourceQ (N : Nat) : Real :=
  (N : Real) * sourceL N ^ (-7 : Int)

/-- The source `T = L^15`. -/
def sourceT (N : Nat) : Real :=
  sourceL N ^ (15 : Nat)

/-- The source `ω = 3.36 P / q`. -/
def omegaCutoff (N q : Nat) : Real :=
  3.36 * sourceP N / (q : Real)

/-- The source `δ(N,q) = 3.36 P / (10 π q N)`. -/
def deltaRadius (N q : Nat) : Real :=
  3.36 * sourceP N / ((10 : Real) * Real.pi * (q : Real) * (N : Real))

/-- The source `δ(q)` from (3.21), indicating whether a fixed exceptional
modulus divides `q`. -/
def exceptionalModulusIndicator (r q : Nat) : Real := by
  classical
  exact if r ∣ q then 1 else 0

/-- The source `δ(χ)` from Theorem 8, indicating the principal character. -/
def deltaCharacter {q : Nat} (chi : Character q) : Real := by
  classical
  exact if chi = 1 then 1 else 0

/-- The center `a / q` appearing in the rational approximation arcs. -/
def rationalCenter (a q : Nat) : Real :=
  (a : Real) / (q : Real)

/-- The full Dirichlet approximation interval `M(a,q)` from (3.2). -/
def approximationArc (N a q : Nat) : Set Real :=
  Set.Icc (rationalCenter a q - 1 / ((q : Real) * sourceQ N))
    (rationalCenter a q + 1 / ((q : Real) * sourceQ N))

/-- The inner core interval from (3.4). -/
def majorCoreArc (N a q : Nat) : Set Real :=
  Set.Icc (rationalCenter a q - deltaRadius N q)
    (rationalCenter a q + deltaRadius N q)

/-- The source admissibility conditions on a Farey index `(a,q)`. -/
def sourceIndex (a q : Nat) : Prop :=
  1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q

/-- The ambient interval `[1 / Q, 1 + 1 / Q]`. -/
def sourceDomain (N : Nat) : Set Real :=
  Set.Icc (1 / sourceQ N) (1 + 1 / sourceQ N)

/-- The first arc family `M1`. -/
def M1 (N : Nat) : Set Real :=
  {α | ∃ (q a : Nat), (q : Real) ≤ sourceP N ∧ sourceIndex a q ∧ α ∈ majorCoreArc N a q}

/-- The second arc family `M2`: the small-denominator approximation arcs with
all of `M1` removed, exactly as in source (3.5). No disjointness theorem is
silently assumed in this definition. -/
def M2 (N : Nat) : Set Real :=
  {α | ∃ (q a : Nat), (q : Real) ≤ sourceP N ∧ sourceIndex a q ∧
      α ∈ approximationArc N a q ∧ α ∉ M1 N}

/-- The third arc family `M3`. -/
def M3 (N : Nat) : Set Real :=
  {α | ∃ (q a : Nat), sourceP N < (q : Real) ∧ (q : Real) ≤ sourceP1 N ∧
      sourceIndex a q ∧ α ∈ approximationArc N a q}

/-- The fourth arc family `M4`. -/
def M4 (N : Nat) : Set Real :=
  sourceDomain N \ (M1 N ∪ M2 N ∪ M3 N)

/-- The source exponential sum `S(α)` on the literal finite window. -/
abbrev S (N : Nat) (α : Real) : Complex :=
  LiuWang.Fourier.liuWangExpSum N α

/-- The source prime weight `log p`, extended by zero off the primes. -/
def primeLogWeight (n : Nat) : Real := by
  classical
  exact if n.Prime then Real.log n else 0

/-- The literal prime-weighted ternary count `I(N)` from (3.9). -/
def I (N : Nat) : Real :=
  ∑ i ∈ windowFinset N, ∑ j ∈ windowFinset N, ∑ k ∈ windowFinset N,
    if i + j + k = N then
      primeLogWeight i * primeLogWeight j * primeLogWeight k
    else 0

/-- The actual finite `Λ`-weighted ternary count provided by the existing
circle-method identity. -/
abbrev lambdaTripleCount (N : Nat) : Real :=
  LiuWang.Fourier.liuWangTernarySum N

/-- The source `J(η)` from (3.22). -/
def J (N : Nat) (η : Real) : Complex :=
  ∫ t in sourceWindowLower N..(N : Real), charReal (η * t)

/-- The source `J(ρ,η)` from (3.22). -/
def Jrho (N : Nat) (rho : Complex) (η : Real) : Complex :=
  ∫ t in sourceWindowLower N..(N : Real), (t : Complex) ^ (rho - 1) * charReal (η * t)

/-- The actual `ψ(x,χ)` endpoint sum already used by the explicit-formula
producer. -/
abbrev psi {q : Nat} (x : Nat) (chi : Character q) : Complex :=
  characterChebyshevSum x chi

/-- The multiplicity-aware completed-zero index used by the explicit formula. -/
abbrev CompletedZeroIndex {q : Nat} [NeZero q] (chi : Character q) :=
  SymmetricCompletedZeroIndex chi

/-- The actual value carried by a multiplicity-aware completed-zero index. -/
abbrev completedZeroValue {q : Nat} [NeZero q] {chi : Character q}
    (p : CompletedZeroIndex chi) : Complex :=
  symmetricCompletedZeroValue p

/-- The critical-strip multiplicity-aware truncation already used in the
explicit-formula producer. -/
abbrev criticalZeroIndices {q : Nat} [NeZero q] (chi : Character q) (T : Real) :=
  criticalStripZeroTruncation chi T

/-- The analytic multiplicity of a zero of `L(s,χ)`. -/
def zeroMultiplicity {q : Nat} [NeZero q] (chi : Character q) (rho : Complex) : Nat :=
  analyticOrderNatAt chi.LFunction rho

/-- The exact primitive-character induction map used throughout the existing
Bombieri–Vinogradov development. -/
def inducedCharacter {q : Nat} [NeZero q] (chi : Character q) :
    Character q :=
  _root_.DirichletCharacter.changeLevel (R := Complex)
    chi.conductor_dvd_level chi.primitiveCharacter

/-- The actual exceptional-zero predicate supplied by the explicit-formula
development. -/
abbrev IsExceptionalZero' {q : Nat} [NeZero q] (c : Real) (chi : Character q) :=
  IsExceptionalZero c chi

/-- The actual faithful optional exceptional-zero selector. -/
abbrev IsExceptionalZeroChoice' {q : Nat} [NeZero q] (c : Real) (chi : Character q) :=
  IsExceptionalZeroChoice c chi

/-- The actual retained-zero predicate used in the primed zero sum. -/
abbrev IsRetainedZero' := IsRetainedZero

/-- The actual truncated critical-zero sum. -/
abbrev truncatedZeroSum {q : Nat} [NeZero q]
    (chi : Character q) (x : Nat) (T : Real) (exceptional : Option Complex) : Complex :=
  truncatedCriticalZeroSum chi x T exceptional

/-- The actual exceptional source term from the explicit formula. -/
abbrev exceptionalSourceTerm (x : Nat) (exceptional : Option Complex) : Complex :=
  exceptionalZeroContribution x exceptional

/-- The actual remainder scale from the explicit formula. -/
abbrev explicitRemainderMajorant := explicitFormulaRemainderMajorant

/-- The actual zero-free data contract used by the explicit formula. -/
abbrev ZeroFreeDataContract {q : Nat} [NeZero q] (c : Real) (chi : Character q) :=
  ExplicitFormulaZeroFreeData c chi

/-- The exact finite-circle consumer proving that the exported `S` and
`lambdaTripleCount` share the existing unit-interval identity. -/
theorem circleIntegral_eq_lambdaTripleCount (N : Nat) :
    (∫ α in (0 : Real)..1, S N α ^ 3 * charReal (-(N : Real) * α)) =
      (lambdaTripleCount N : Complex) := by
  simpa [S, lambdaTripleCount] using LiuWang.Fourier.integral_liuWangExpSum_cube N 0

/-- The primitive-character source really induces back to the ambient
character by the existing `changeLevel` map. -/
theorem inducedCharacter_eq_self {q : Nat} [NeZero q] (chi : Character q) :
    inducedCharacter chi = chi := by
  simpa [inducedCharacter] using chi.changeLevel_primitiveCharacter

/-- Nonprincipality is preserved when passing to the actual primitive source. -/
theorem primitiveCharacter_ne_one_of_ne_one {q : Nat} [NeZero q]
    (chi : Character q) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 :=
  BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi

/-- In the positive half-plane, the completed-function multiplicity agrees with
the analytic multiplicity of `L(s,χ)`. -/
theorem completedMultiplicity_eq_zeroMultiplicity {q : Nat} [NeZero q]
    {chi : Character q} (hchi : chi ≠ 1) {rho : Complex} (hrho : 0 < rho.re) :
    analyticOrderNatAt (symmetricCompletedLFunction chi) rho =
      zeroMultiplicity chi rho := by
  simpa [zeroMultiplicity] using
    analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction
      (chi := chi) hchi hrho

/-- Every multiplicity-aware completed-zero index maps to an actual zero. -/
theorem completedZeroValue_apply_eq_zero' {q : Nat} [NeZero q]
    {chi : Character q} (hchi : chi ≠ 1) (p : CompletedZeroIndex chi) :
    symmetricCompletedLFunction chi (completedZeroValue p) = 0 :=
  symmetricCompletedZeroValue_apply_eq_zero hchi p

/-- Primitive completed-zero values lie in the open critical strip. -/
theorem completedZeroValue_re_mem_Ioo {q : Nat} [NeZero q]
    {chi : Character q} (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : CompletedZeroIndex chi) :
    Set.Ioo 0 1 (completedZeroValue p).re :=
  symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p

/-- The explicit-formula development always provides an actual optional
exceptional choice. -/
theorem exists_exceptionalZeroChoice (c : Real) {q : Nat} [NeZero q] (chi : Character q) :
    ∃ exceptional : Option Complex, IsExceptionalZeroChoice' c chi exceptional :=
  exists_faithfulExceptionalChoice c chi

/-- The actual zero-free region contract. -/
theorem dirichletZeroFreeRegion_contract :
    exists c : Real, 0 < c ∧
      forall {q : Nat} [NeZero q] (chi : Character q),
        chi ≠ 1 ->
          (forall s : Complex, 0 < s.re -> chi.LFunction s = 0 ->
            (chi ^ 2 ≠ 1 ∨ s.im ≠ 0) ->
              c / (Real.log q + Real.log (|s.im| + 2)) ≤ 1 - s.re) ∧
          (forall s t : Complex,
            0 < s.re -> 0 < t.re ->
            chi.LFunction s = 0 -> chi.LFunction t = 0 ->
            s.im = 0 -> t.im = 0 ->
            1 - s.re ≤ c / Real.log q ->
            1 - t.re ≤ c / Real.log q -> s = t) ∧
          (forall s : Complex, 0 < s.re -> chi.LFunction s = 0 ->
            s.im = 0 -> 1 - s.re ≤ c / Real.log q ->
              analyticOrderNatAt chi.LFunction s = 1) :=
  dirichletZeroFreeRegion

/-- The actual uniform zero-free data package used by the explicit formula. -/
theorem exists_zeroFreeDataContract :
    exists c : Real, And (0 < c)
      (forall {q : Nat} [NeZero q] (chi : Character q),
        3 <= q -> Ne chi 1 -> ZeroFreeDataContract c chi) :=
  exists_explicitFormulaZeroFreeData

/-- The actual explicit-formula contract consumed downstream. -/
theorem dirichletExplicitFormula_contract :
    exists c : Real, And (0 < c)
      (And (forall {q : Nat} [NeZero q] (chi : Character q),
        Ne chi 1 -> ZeroFreeDataContract c chi)
      (exists C : Real, And (0 < C)
        (forall {q : Nat} [NeZero q] {chi : Character q},
          Ne chi 1 -> forall {x : Nat}, 2 <= x ->
            forall {T : Real}, 2 <= T -> T <= x ->
              forall (exceptional : Option Complex),
                IsExceptionalZeroChoice' c chi exceptional ->
                  norm (psi x chi + truncatedZeroSum chi x T exceptional +
                    exceptionalSourceTerm x exceptional) <=
                    C * explicitRemainderMajorant q x T))) :=
  dirichletExplicitFormula

end LiuWang.Proof.Interfaces
