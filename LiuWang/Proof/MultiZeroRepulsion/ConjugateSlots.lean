import LiuWang.Proof.MultiZeroRepulsion.ProductCount
import BombieriVinogradov.Helpers.ComplexAnalysis.AnalyticOrderConjugation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionConjugation

/-! Conjugation preserves character labels and each actual analytic multiplicity slot. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion

theorem ordinary_order_conjugate {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : 0 < rho.re) (hr1 : rho.re < 1) :
    analyticOrderNatAt chi⁻¹.LFunction (conj rho) = analyticOrderNatAt chi.LFunction rho := by
  by_cases hc : chi = 1
  · subst chi
    have hn : rho ≠ 1 := by intro he; simp [he] at hr1
    have hcn : conj rho ≠ 1 := by
      intro he
      apply hn
      simpa using congrArg conj he
    rw [inv_one, ← PrincipalPsi.Quantitative.analyticOrderNatAt_xi_eq_principal
      (q := q) (by simpa using hr) hcn,
      ← PrincipalPsi.Quantitative.analyticOrderNatAt_xi_eq_principal (q := q) hr hn]
    have hh := BombieriVinogradov.ComplexAnalysis.AnalyticAt.analyticOrderNatAt_conj_conj
      (f := riemannXi) (z := conj rho) (differentiable_riemannXi.analyticAt _)
    have hf : (fun z => conj (riemannXi (conj z))) = riemannXi :=
      funext (fun z => (xi_conj z).symm)
    rw [hf] at hh
    simpa only [Complex.conj_conj] using hh
  · have hf : chi⁻¹.LFunction = fun z => conj (chi.LFunction (conj z)) :=
      funext (DirichletCharacter.LFunction_inv_eq_conj_conj hc)
    rw [hf]
    have hh := BombieriVinogradov.ComplexAnalysis.AnalyticAt.analyticOrderNatAt_conj_conj
      (f := chi.LFunction) (z := conj rho)
      ((DirichletCharacter.differentiable_LFunction hc).analyticAt _)
    simpa only [Complex.conj_conj] using hh

theorem strict_zero_conjugate {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {alpha y : ℝ} {rho : ℂ} (hrho : rho ∈ strictZeroValues chi alpha y) :
    conj rho ∈ strictZeroValues chi⁻¹ alpha y := by
  obtain ⟨hz, h0, ha, h1, ht⟩ := mem_strictZeroValues.mp hrho
  have hn : rho ≠ 1 := by intro he; simp [he] at h1
  have hcn : conj rho ≠ 1 := by intro he; have := congrArg Complex.re he; simp at this; linarith
  have hzero : chi⁻¹.LFunction (conj rho) = 0 := by
    by_cases hc : chi = 1
    · subst chi
      rw [inv_one]
      apply (PrincipalPsi.principal_zero_iff_zeta_zero (by simpa using h0) hcn).mpr
      rw [riemannZeta_conj, (PrincipalPsi.principal_zero_iff_zeta_zero h0 hn).mp hz, map_zero]
    · rw [DirichletCharacter.LFunction_inv_eq_conj_conj hc, Complex.conj_conj, hz, map_zero]
  exact mem_strictZeroValues.mpr
    ⟨hzero, by simpa using h0, by simpa using ha, by simpa using h1, by simpa using ht⟩

def conjugateSlot {q : ℕ} [NeZero q] {alpha y : ℝ} (p : ZeroSlots q alpha y) :
    ZeroSlots q alpha y where
  character := p.character⁻¹
  value := conj p.value
  index := p.index
  zero_mem := strict_zero_conjugate p.zero_mem
  index_lt := by
    rw [ordinary_order_conjugate p.character
      (mem_strictZeroValues.mp p.zero_mem).2.1
      (mem_strictZeroValues.mp p.zero_mem).2.2.2.1]
    exact p.index_lt

theorem conjugateSlot_character {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q alpha y) : (conjugateSlot p).character = p.character⁻¹ := rfl

theorem conjugateSlot_value {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q alpha y) : (conjugateSlot p).value = conj p.value := rfl

theorem conjugateSlot_index {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q alpha y) : (conjugateSlot p).index = p.index := rfl

theorem zeroSlots_ext {q : ℕ} [NeZero q] {alpha y : ℝ} {p r : ZeroSlots q alpha y}
    (hc : p.character = r.character) (hv : p.value = r.value) (hm : p.index = r.index) : p = r := by
  rcases p with ⟨chi, rho, k, hrho, hk⟩
  rcases r with ⟨psi, tau, l, htau, hl⟩
  dsimp at hc hv hm
  subst psi
  subst tau
  subst l
  rfl

theorem conjugateSlot_involutive {q : ℕ} [NeZero q] {alpha y : ℝ} :
    Function.Involutive (@conjugateSlot q _ alpha y) := by
  intro p
  apply zeroSlots_ext
  · rw [conjugateSlot_character, conjugateSlot_character, inv_inv]
  · rw [conjugateSlot_value, conjugateSlot_value, Complex.conj_conj]
  · rw [conjugateSlot_index, conjugateSlot_index]

def conjugateSlotsEquiv (q : ℕ) [NeZero q] (alpha y : ℝ) :
    ZeroSlots q alpha y ≃ ZeroSlots q alpha y :=
  ⟨conjugateSlot, conjugateSlot, conjugateSlot_involutive, conjugateSlot_involutive⟩

theorem conjugateSlot_fixed_iff {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q alpha y) :
    conjugateSlot p = p ↔ p.character⁻¹ = p.character ∧ p.value.im = 0 := by
  constructor
  · intro he
    have hc := congrArg (fun z : ZeroSlots q alpha y => z.character) he
    have hv := congrArg (fun z : ZeroSlots q alpha y => z.value) he
    rw [conjugateSlot_character] at hc
    rw [conjugateSlot_value] at hv
    have hi := congrArg Complex.im hv
    simp only [conj_im] at hi
    exact ⟨hc, by linarith⟩
  · rintro ⟨hc, hi⟩
    apply zeroSlots_ext
    · exact (conjugateSlot_character p).trans hc
    · rw [conjugateSlot_value]
      apply Complex.ext <;> simp [hi]
    · exact conjugateSlot_index p

end LiuWang.Proof.MultiZeroRepulsion
