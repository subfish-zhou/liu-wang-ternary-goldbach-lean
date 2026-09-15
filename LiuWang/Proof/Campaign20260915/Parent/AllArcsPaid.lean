import LiuWang.Proof.Campaign20260915.Parent.SourceSplitSecondPaid
import LiuWang.Proof.Campaign20260915.Parent.RecoveredThirdArc
import LiuWang.Proof.Campaign20260915.Totient.Cutoff

/-! Original large-odd-N conclusion with four shared mathematical inputs.
These are explicit unproved inputs, not axioms declared in the environment.
No arc estimate, source existence, or selected-zero classification is assumed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Parent.AllArcsPaid

section SmallConductors
variable (hsmall : ∀ (q : ℕ) [NeZero q] (chi : Character q),
    chi.IsPrimitive → chi ≠ 1 → chi ^ 2 = 1 → ∀ x beta : ℝ,
    10 ≤ x → (q : ℝ) ≤ x →
    1 - 1 / (9.645908801 * Real.log x) ≤ beta →
    chi.LFunction (beta : ℂ) = 0 → 987 ≤ q)

include hsmall

theorem paper_conductor {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    987 ≤ (d.modulus : ℝ) := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have he : (e.re : ℂ) = e := by
    apply Complex.ext <;> simp [hd.2.2.1]
  have h := hsmall d.modulus d.character d.isPrimitive d.ne_one d.square_eq_one
    (sourceP N) e.re (by linarith [OriginalRegion.sourceP_original_scale hN])
    hd.1 hd.2.2.2.2.le (by simpa only [ZeroRegionFamily.datumL, he] using hd.2.1)
  exact_mod_cast h

theorem third_conductor {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N < (q : ℝ))
    (chi : Character q) (rho : ℂ) (hz : chi.LFunction rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1)
    (ht : |rho.im| ≤ LiuWang.Proof.SourceRoute.ThirdArc.lowHeight)
    (hr : Source525526.lastUpper q < rho.re) : 987 ≤ chi.conductor := by
  have hd := Source525526.theorem_two_low_domain hN hq.le
  have hc := OriginalRegion.source_free_original_classification hd.1 hd.2.1 chi
    hr h1 (by simpa only [hd.2.2] using ht) hz
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hn := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc.1
  have hs := BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one
    chi hc.2.1
  have he : (rho.re : ℂ) = rho := by
    apply Complex.ext <;> simp [hc.2.2.1]
  have hz' := BombieriVinogradov.SiegelWalfisz.primitive_LFunction_eq_zero_of_LFunction_eq_zero
    chi hc.1 h0 hz
  have hlevel : (chi.conductor : ℝ) ≤ (q : ℝ) * LiuWang.Proof.SourceRoute.ThirdArc.lowHeight :=
    (by exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi :
      (chi.conductor : ℝ) ≤ q).trans hd.2.1
  exact hsmall chi.conductor chi.primitiveCharacter chi.primitiveCharacter_isPrimitive hn hs
    ((q : ℝ) * LiuWang.Proof.SourceRoute.ThirdArc.lowHeight) rho.re
    (by linarith [hd.1]) hlevel hr.le (by simpa only [he] using hz')
end SmallConductors

/-- All original arc budgets consumed. The four shared inputs remain unproved here. -/
theorem threeOddPrimes_of_four_shared_inputs {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hdensity : ∀ (q : ℕ) [NeZero q], ∀ alpha y : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
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
  have hphi : ∀ d e, PaperSource N d e →
      (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤
      LiuWang.Proof.SourceRoute.MajorException.Continuation.nu d.modulus := by
    intro d e hd
    have hh : 987 ≤ d.modulus := by exact_mod_cast paper_conductor hsmall hN hd
    exact htotient d.modulus (by omega)
  apply SourceSplitSecondPaid.threeOddPrimes_of_shared_inputs_and_third hN hodd
    (fun _ _ hd => paper_conductor hsmall hN hd) hphi hzeta
    (fun q _ _ alpha y h0 h1 hy => hdensity q alpha y h0 h1 hy)
    (fun q _ hq => Totient.second_arc_totient_input_of_RS (q := q) hN hq htotient)
  apply RecoveredThirdArc.M3_original_local_energy hN
  · intro q hq _
    have hh : (3 : ℝ) ≤ q := by linarith [OriginalRegion.sourceP_original_scale hN]
    exact htotient q (by exact_mod_cast hh)
  · intro q _ _ _ y alpha hy h0 h1
    exact hdensity q alpha y h0 h1 hy
  · intro q _ hq _ chi rho hz h0 h1 ht hr
    exact third_conductor hsmall hN hq chi rho hz h0 h1 ht hr

#print axioms paper_conductor
#print axioms third_conductor
#print axioms threeOddPrimes_of_four_shared_inputs
end LiuWang.Proof.Campaign20260915.Parent.AllArcsPaid
