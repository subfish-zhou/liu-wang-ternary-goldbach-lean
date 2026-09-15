import LiuWang.Proof.Campaign20260915.OriginalRegion.SourceFreeRegion

/-! Whole-family uniqueness and actual analytic multiplicity, without a preselected source. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem source_free_original_zeros_equal_closed {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) (chi psi : DirichletCharacter ℂ q)
    {rho tau : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re) (hr1 : rho.re < 1)
    (hs : 1 - 1 / (9.645908801 * Real.log x) ≤ tau.re) (hs1 : tau.re < 1)
    (ht : |rho.im| ≤ x / q) (hu : |tau.im| ≤ x / q)
    (hz : chi.LFunction rho = 0) (hw : psi.LFunction tau = 0) :
    chi = psi ∧ rho = tau := by
  obtain ⟨hc0, hc2, hi, _⟩ := source_free_original_classification_closed hx hq chi hr hr1 ht hz
  obtain ⟨hp0, hp2, hj, _⟩ := source_free_original_classification_closed hx hq psi hs hs1 hu hw
  have hL : 0 < Real.log x := by linarith [source_log_twenty_two hx]
  have hgap : 1 / (9.645908801 * Real.log x) < 1 / (8 * Real.log x) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hf : (tau.re : ℂ) = tau := by apply Complex.ext <;> simp [hj]
  obtain ⟨d, _, _, _, hd, _, _, hall⟩ :=
    real_family_fixed_source_eight (by linarith : 10 ≤ x) hq chi hc0 hc2
      (beta := rho.re) (by linarith) (by simpa only [he] using hz)
  obtain ⟨heq, _, _, hd', _⟩ := hall q hq psi tau.re hp0 hp2 (by linarith)
    (by simpa only [hf] using hw)
  refine ⟨hd.symm.trans hd', ?_⟩
  rw [← he, ← hf, heq]

def OriginalClosedZeros (x : ℝ) (q : ℕ) [NeZero q] :=
  Σ z : {z : DirichletCharacter ℂ q × ℂ //
    1 - 1 / (9.645908801 * Real.log x) ≤ z.2.re ∧ z.2.re < 1 ∧
    |z.2.im| ≤ x / q ∧ z.1.LFunction z.2 = 0},
    Fin (analyticOrderNatAt z.val.1.LFunction z.val.2)

theorem originalClosedZeros_subsingleton {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) : Subsingleton (OriginalClosedZeros x q) := by
  refine ⟨?_⟩
  rintro ⟨z, i⟩ ⟨w, j⟩
  have hc := z.property
  have hp := w.property
  have he := source_free_original_zeros_equal_closed hx hq z.val.1 w.val.1
    hc.1 hc.2.1 hp.1 hp.2.1 hc.2.2.1 hp.2.2.1 hc.2.2.2 hp.2.2.2
  have hzw : z = w := Subtype.ext (Prod.ext he.1 he.2)
  subst w
  have hm := (source_free_original_classification_closed hx hq z.val.1
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).2.2.2
  have hij : i = j := by
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_le i.isLt hm.le
    have hj : j.val < 1 := lt_of_lt_of_le j.isLt hm.le
    omega
  subst j
  rfl

theorem source_free_original_option {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    ∃ e : Option (DirichletCharacter ℂ q × ℂ),
      (∀ chi rho,
        (1 - 1 / (9.645908801 * Real.log x) < rho.re ∧ rho.re < 1 ∧
          |rho.im| ≤ x / q ∧ chi.LFunction rho = 0) ↔ e = some (chi, rho)) ∧
      (∀ z, e = some z →
        z.1 ≠ 1 ∧ z.1 ^ 2 = 1 ∧ z.2.im = 0 ∧ analyticOrderNatAt z.1.LFunction z.2 = 1) := by
  let P (z : DirichletCharacter ℂ q × ℂ) :=
    1 - 1 / (9.645908801 * Real.log x) < z.2.re ∧ z.2.re < 1 ∧
      |z.2.im| ≤ x / q ∧ z.1.LFunction z.2 = 0
  by_cases hex : ∃ z, P z
  · obtain ⟨z, hz⟩ := hex
    refine ⟨some z, ?_, ?_⟩
    · intro chi rho
      constructor
      · intro h
        have he := source_free_original_zeros_equal_closed hx hq z.1 chi
          hz.1.le hz.2.1 h.1.le h.2.1 hz.2.2.1 h.2.2.1 hz.2.2.2 h.2.2.2
        exact congrArg some (Prod.ext he.1 he.2)
      · intro h
        have he := Option.some.inj h
        simpa only [he] using hz
    · intro w hw
      have he := Option.some.inj hw
      subst w
      exact source_free_original_classification hx hq z.1 hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  · refine ⟨none, ?_, ?_⟩
    · intro chi rho
      constructor
      · exact fun h => False.elim (hex ⟨(chi, rho), h⟩)
      · intro h
        cases h
    · intro z h
      cases h

end LiuWang.Proof.Campaign20260915.OriginalRegion
