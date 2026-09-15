import LiuWang.Proof.SourceRoute.MajorException.ConductorReduction

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException

inductive PureKind
  | linear
  | quadratic
  | cubic
  deriving DecidableEq

def pureTerm {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) (beta : ℝ) :
    PureKind → ℂ
  | .linear => linearTerm N chi beta
  | .quadratic => quadraticTerm N chi beta
  | .cubic => cubicTerm N chi beta

def sourceMomentFactor (N : ℕ) (beta : ℝ) : PureKind → ℝ
  | .linear => 2.8959*(N : ℝ)^2*baseWeight N beta
  | .quadratic => (3*quadraticHolderConstant)*(N : ℝ)^2*baseWeight N beta^2
  | .cubic => (3*1.0302*1.0033^2/Real.pi)*(N : ℝ)^2*baseWeight N beta^3

def sourceArithmeticFactor (q d : ℕ) : PureKind → ℝ
  | .linear => moebiusWeight q*Real.sqrt d/(q.totient : ℝ)^2
  | .quadratic => moebiusWeight q*(d : ℝ)/(q.totient : ℝ)^2
  | .cubic => (d : ℝ)*Real.sqrt d/(q.totient : ℝ)^2

def reducedArithmeticFactor (X d : ℕ) : PureKind → ℝ
  | .linear => (moebiusWeight d*Real.sqrt d/(d.totient : ℝ)^2) *
      squarefreeTotientMass (X/d)
  | .quadratic => (moebiusWeight d*(d : ℝ)/(d.totient : ℝ)^2) *
      squarefreeTotientMass (X/d)
  | .cubic => ((d : ℝ)*Real.sqrt d/(d.totient : ℝ)^2) * totientMass (X/d)

theorem sourceMomentFactor_nonneg (N : ℕ) (beta : ℝ) (j : PureKind) :
    0 ≤ sourceMomentFactor N beta j := by
  cases j <;> dsimp [sourceMomentFactor, quadraticHolderConstant, baseWeight] <;> positivity

theorem sourceArithmeticFactor_nonneg (q d : ℕ) (j : PureKind) :
    0 ≤ sourceArithmeticFactor q d j := by
  cases j <;> dsimp [sourceArithmeticFactor, moebiusWeight] <;> positivity

theorem pureTerm_source_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) {beta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) (j : PureKind) :
    ‖pureTerm N chi beta j‖ ≤
      sourceMomentFactor N beta j * sourceArithmeticFactor q chi.conductor j := by
  cases j with
  | linear => exact linearTerm_source_bound hN chi hb hb1
  | quadratic => exact quadraticTerm_source_bound hN chi hb hb1
  | cubic => exact cubicTerm_source_bound hN chi hb hb1

theorem sourceArithmetic_reduction (X : ℕ) {d : ℕ} (hd : 0 < d) (j : PureKind) :
    (∑ q ∈ Finset.Icc 1 X, if d ∣ q then sourceArithmeticFactor q d j else 0) ≤
      reducedArithmeticFactor X d j := by
  cases j with
  | linear => exact source_linear_conductor_reduction X hd
  | quadratic => exact source_quadratic_conductor_reduction X hd
  | cubic => exact source_cubic_conductor_reduction X hd

def selectedPureArc (N q : ℕ) (j : PureKind) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : Character q, ∑ rho ∈ exceptionalValues N chi, pureTerm N chi rho.re j

theorem selectedPureArc_eq {q : ℕ} [NeZero q] (N : ℕ) (j : PureKind) :
    selectedPureArc N q j =
      ∑ chi : Character q, ∑ rho ∈ exceptionalValues N chi, pureTerm N chi rho.re j := by
  simp only [selectedPureArc, dif_neg (NeZero.ne q)]

theorem selectedPureArc_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (j : PureKind) :
    selectedPureArc N q j = pureTerm N chi rho.re j := by
  rw [selectedPureArc_eq, Fintype.sum_eq_single chi]
  · rw [exceptionalValues_at_witness hN hq hr, Finset.sum_singleton]
  · intro psi hpsi
    rw [exceptionalValues_other_character hN hq hr hpsi, Finset.sum_empty]

theorem selectedPureArc_no_exception {q : ℕ} [NeZero q] (N : ℕ)
    (hn : ∀ chi : Character q, exceptionalValues N chi = ∅) (j : PureKind) :
    selectedPureArc N q j = 0 := by
  simp only [selectedPureArc_eq, hn, Finset.sum_empty, Finset.sum_const_zero]

theorem exceptionalArc_eq_selected {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    exceptionalArc N q =
      selectedPureArc N q .linear + selectedPureArc N q .quadratic +
        selectedPureArc N q .cubic := by
  by_cases hex : ∃ (chi : Character q) (rho : ℂ), rho ∈ exceptionalValues N chi
  · obtain ⟨chi, rho, hr⟩ := hex
    simp only [selectedPureArc_at_witness hN hq hr, pureTerm]
    exact exceptionalArc_eq_source_terms hN hq hr
  · have hn : ∀ chi : Character q, exceptionalValues N chi = ∅ :=
      fun chi => Finset.eq_empty_iff_forall_notMem.mpr (fun rho hr => hex ⟨chi, rho, hr⟩)
    simp only [(exceptionalArc_no_exception N hn).1, selectedPureArc_no_exception N hn,
      add_zero]

def selectedPureIntegral (N : ℕ) (j : PureKind) : ℂ :=
  ∑ q ∈ denominators (sourceP N), selectedPureArc N q j

theorem exceptionalIntegral_eq_selected {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    exceptionalIntegral N =
      selectedPureIntegral N .linear + selectedPureIntegral N .quadratic +
        selectedPureIntegral N .cubic := by
  rw [exceptionalIntegral, coreIndices, Finset.sum_sigma]
  change (∑ q ∈ denominators (sourceP N), exceptionalArc N q) = _
  simp only [selectedPureIntegral, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := (mem_denominators (sourceP_pos hN).le q).mp hq
  let : NeZero q := ⟨by omega⟩
  exact exceptionalArc_eq_selected hN hq'.2

theorem fixed_source_pure_totals {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      ∀ j : PureKind,
        (∑ s ∈ denominators (sourceP N), ‖selectedPureArc N s j‖) ≤
          sourceMomentFactor N rho.re j *
            reducedArithmeticFactor ⌊sourceP N⌋₊ d.modulus j := by
  obtain ⟨d, _, hdc, _, _, hall⟩ := exceptionalValues_same_source hN hq hr
  refine ⟨d, hdc, ?_⟩
  intro j
  have hd : 0 < d.modulus := by
    rw [hdc]
    exact Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hb := exceptional_beta_source_range hN hr
  have hlocal (s : ℕ) (hs : s ∈ denominators (sourceP N)) :
      ‖selectedPureArc N s j‖ ≤ sourceMomentFactor N rho.re j *
        (if d.modulus ∣ s then sourceArithmeticFactor s d.modulus j else 0) := by
    have hs' := (mem_denominators (sourceP_pos hN).le s).mp hs
    let : NeZero s := ⟨by omega⟩
    by_cases hex : ∃ (psi : Character s) (tau : ℂ), tau ∈ exceptionalValues N psi
    · obtain ⟨psi, tau, ht⟩ := hex
      have hsrc := hall s hs'.2 psi tau ht
      rw [selectedPureArc_at_witness hN hs'.2 ht, hsrc.1, if_pos hsrc.2.2.1]
      simpa only [hsrc.2.1] using pureTerm_source_bound hN psi hb.1 hb.2 j
    · have hn : ∀ psi : Character s, exceptionalValues N psi = ∅ :=
        fun psi => Finset.eq_empty_iff_forall_notMem.mpr (fun tau ht => hex ⟨psi, tau, ht⟩)
      rw [selectedPureArc_no_exception N hn, norm_zero]
      exact mul_nonneg (sourceMomentFactor_nonneg N rho.re j)
        (by split_ifs; exact sourceArithmeticFactor_nonneg s d.modulus j; rfl)
  apply (Finset.sum_le_sum hlocal).trans
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sourceArithmetic_reduction ⌊sourceP N⌋₊ hd j)
    (sourceMomentFactor_nonneg N rho.re j)

theorem fixed_source_pure_integrals {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      ∀ j : PureKind, ‖selectedPureIntegral N j‖ ≤
        sourceMomentFactor N rho.re j *
          reducedArithmeticFactor ⌊sourceP N⌋₊ d.modulus j := by
  obtain ⟨d, hdc, hall⟩ := fixed_source_pure_totals hN hq hr
  exact ⟨d, hdc, fun j => (norm_sum_le _ _).trans (hall j)⟩

end LiuWang.Proof.SourceRoute.MajorException
