import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.Ledger

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

def principalCount {d e f : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f) : ℕ :=
  (if chi = 1 then 1 else 0) + (if psi = 1 then 1 else 0) + (if eta = 1 then 1 else 0)

theorem principalCount_zero_iff {d e f : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f) :
    principalCount chi psi eta = 0 ↔ chi ≠ 1 ∧ psi ≠ 1 ∧ eta ≠ 1 := by
  unfold principalCount
  split_ifs <;> simp_all

theorem original_eight_exhaustion {d e f q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (hd : d ∣ q) (he : e ∣ q) (hf : f ∣ q) :
    principalCount chi psi eta = 3 ∨
    principalCount chi psi eta = 2 ∨
    principalCount chi psi eta = 1 ∨
    (principalCount chi psi eta = 0 ∧ pairCount chi psi eta = 0 ∧
      lwdProduct (lwdProduct chi psi) eta ≠ 1) ∨
    (principalCount chi psi eta = 0 ∧ pairCount chi psi eta = 1 ∧
      lwdProduct (lwdProduct chi psi) eta ≠ 1) ∨
    (principalCount chi psi eta = 0 ∧ pairCount chi psi eta = 2 ∧
      lwdProduct (lwdProduct chi psi) eta ≠ 1) ∨
    (principalCount chi psi eta = 0 ∧ pairCount chi psi eta = 3 ∧
      lwdProduct (lwdProduct chi psi) eta ≠ 1) ∨
    (principalCount chi psi eta = 0 ∧ pairCount chi psi eta = 0 ∧
      lwdProduct (lwdProduct chi psi) eta = 1) := by
  have hn : principalCount chi psi eta ≤ 3 := by
    unfold principalCount
    split_ifs <;> norm_num
  by_cases h0 : principalCount chi psi eta = 0
  · have hc := (principalCount_zero_iff chi psi eta).mp h0
    by_cases ht : lwdProduct (lwdProduct chi psi) eta = 1
    · have hp := (pairCount_zero_iff chi psi eta).mpr
        (triple_principal_no_pair chi psi eta hd he hf hc.1 hc.2.1 hc.2.2 ht)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, hp, ht⟩))))))
    · have hp := pairCount_le_three chi psi eta
      have hn' : pairCount chi psi eta = 0 ∨ pairCount chi psi eta = 1 ∨
          pairCount chi psi eta = 2 ∨ pairCount chi psi eta = 3 := by omega
      refine Or.inr (Or.inr (Or.inr ?_))
      rcases hn' with h1 | h1 | h1 | h1
      · exact Or.inl ⟨h0, h1, ht⟩
      · exact Or.inr (Or.inl ⟨h0, h1, ht⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h0, h1, ht⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1, ht⟩)))
  · have hn' : principalCount chi psi eta = 3 ∨ principalCount chi psi eta = 2 ∨
        principalCount chi psi eta = 1 := by omega
    rcases hn' with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))

theorem counted_primitive_zero {d q : ℕ} [NeZero d] [NeZero q] {alpha y : ℝ}
    (chi : DirichletCharacter ℂ d) (hd : d ∣ q) (p : ZeroSlots q alpha y)
    (hl : p.character = chi.changeLevel hd) : chi.LFunction p.value = 0 := by
  have hz := mem_strictZeroValues.mp p.zero_mem
  have ho := common_lift_order p.character chi (dvd_refl q) hd
    (by simpa only [DirichletCharacter.changeLevel_self] using hl) hz.2.1 hz.2.2.2.1
  have hi := p.index_lt
  rw [ho] at hi
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by omega)

theorem counted_g_by_eight_cases {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x alpha : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {p r u : ZeroSlots q alpha (x / q)}
    (h : CountedData x q alpha chi psi eta p r u)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi psi eta (lwdSourceSigma x) p.value.im r.value.im u.value.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - p.value.re) + 1 / (lwdSourceSigma x - r.value.re) +
          1 / (lwdSourceSigma x - u.value.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  rcases original_eight_exhaustion chi psi eta h.chi_dvd h.psi_dvd h.eta_dvd with
    _hi | _hii | _hiii | hiv | _hv | _hvi | _hvii | _hviii
  · exact counted_g_le h hRS hgammaHigh hgammaLow
  · exact counted_g_le h hRS hgammaHigh hgammaLow
  · exact counted_g_le h hRS hgammaHigh hgammaLow
  · have hc := (principalCount_zero_iff chi psi eta).mp hiv.1
    have hp := (pairCount_zero_iff chi psi eta).mp hiv.2.1
    have hz1 := mem_strictZeroValues.mp p.zero_mem
    have hz2 := mem_strictZeroValues.mp r.zero_mem
    have hz3 := mem_strictZeroValues.mp u.zero_mem
    exact lwd_2_27_case_iv h.scale_ge h.level_le h.chi_dvd h.psi_dvd h.eta_dvd chi psi eta
      hc.1 hc.2.1 hc.2.2 h.chi_primitive h.psi_primitive h.eta_primitive hp.1 hp.2.1 hp.2.2 hiv.2.2
      h.re_gt_half.1 hz1.2.2.2.1 (counted_primitive_zero chi h.chi_dvd p h.p_label)
      h.re_gt_half.2.1 hz2.2.2.2.1 (counted_primitive_zero psi h.psi_dvd r h.r_label)
      h.re_gt_half.2.2 hz3.2.2.2.1 (counted_primitive_zero eta h.eta_dvd u h.u_label)
      hz1.2.2.2.2 hz2.2.2.2.2 hz3.2.2.2.2
  · exact counted_g_le h hRS hgammaHigh hgammaLow
  · exact counted_g_le h hRS hgammaHigh hgammaLow
  · exact counted_g_le h hRS hgammaHigh hgammaLow
  · exact counted_g_le h hRS hgammaHigh hgammaLow

theorem counted_eight_case_2_28 {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x alpha : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {p r u : ZeroSlots q alpha (x / q)}
    (h : CountedData x q alpha chi psi eta p r u)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    0 ≤ 1 / (lwdSourceSigma x - 1) -
      (1 / (lwdSourceSigma x - p.value.re) + 1 / (lwdSourceSigma x - r.value.re) +
        1 / (lwdSourceSigma x - u.value.re)) +
      7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  have hb (b c : Bool) := counted_g_by_eight_cases (counted_data_signed h false b c)
    hRS hgammaHigh hgammaLow
  have h0 := hb false false
  have h1 := hb true false
  have h2 := hb false true
  have h3 := hb true true
  simp only [signedSlot, lwdSignedCharacter, Bool.false_eq_true, if_false, if_true,
    conjugateSlot_value, conj_re, conj_im] at h0 h1 h2 h3
  have hpos := lwd_2_13 chi psi eta (lwd_source_parameters h.scale_ge).2.2.1
    p.value.im r.value.im u.value.im
  linarith only [hpos, h0, h1, h2, h3]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples
