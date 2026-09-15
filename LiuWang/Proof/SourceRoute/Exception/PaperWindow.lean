import LiuWang.Proof.SourceRoute.Exception.StrictRepulsion

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.Exception

theorem original_seed_low_lambda {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) {e : ℂ}
    (he : 1 - 1 / (9.645908801 * Real.log (sourceP N)) ≤ e.re) :
    (1 - e.re) * Real.log (lowScale N) ≤ 0.11 := by
  have hlog : 0 < Real.log (lowScale N) := by
    have h : (25 : ℝ) ≤ Real.log (lowScale N) :=
      (log_scale_bounds (sourceL_ge_3100 hN)).1
    linarith
  apply (le_div_iff₀ hlog).mp
  linarith [paper_gap_le_low_gap hN]

theorem original_complex_seed_repulsion {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (chi psi : Character q) {e rho : ℂ}
    (he : e ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hr : rho ∈ CompleteExpansion.zeroValues psi (omegaCutoff N q))
    (hbound : 1 - 1 / (9.645908801 * Real.log (sourceP N)) ≤ e.re)
    (hne : psi ≠ chi ∨ rho ≠ e)
    (hnc : psi ≠ chi⁻¹ ∨ rho ≠ conj e) :
    rho.re < cap N 0.3221 := by
  obtain ⟨hx, hqx, hy⟩ := low_scale_table_domain hN hq
  have hl := original_seed_low_lambda hN hbound
  exact actual_zero_repulsion hx hqx chi psi (by simpa only [hy] using he)
    (by simpa only [hy] using hr) hne hnc (by linarith)

theorem original_seed_closed_cap_pair {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (chi psi : Character q) {e rho : ℂ}
    (he : e ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hr : rho ∈ CompleteExpansion.zeroValues psi (omegaCutoff N q))
    (hbound : 1 - 1 / (9.645908801 * Real.log (sourceP N)) ≤ e.re)
    (hcap : cap N 0.3221 ≤ rho.re) :
    (psi = chi ∧ rho = e) ∨ (psi = chi⁻¹ ∧ rho = conj e) := by
  by_contra hn
  have hne : psi ≠ chi ∨ rho ≠ e := by tauto
  have hnc : psi ≠ chi⁻¹ ∨ rho ≠ conj e := by tauto
  exact (not_lt_of_ge hcap)
    (original_complex_seed_repulsion hN hq chi psi he hr hbound hne hnc)

theorem paper_induced_inverse {q : ℕ} [NeZero q]
    (d : PrimitiveQuadraticDatum) (hdiv : d.modulus ∣ q) :
    (inducedAt d q)⁻¹ = inducedAt d q := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have hd : d.character⁻¹ = d.character := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using d.square_eq_one)
  rw [inducedAt, dif_pos hdiv]
  simpa only [map_inv] using congrArg (DirichletCharacter.changeLevel hdiv) hd

theorem paper_source_retained_strict {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) (psi : Character q) {rho : ℂ}
    (hr : rho ∈ retainedValues psi (omegaCutoff N q) d e) :
    rho.re < cap N 0.3221 := by
  obtain ⟨hz, hret⟩ := Finset.mem_filter.mp hr
  have he := (paper_induced_mem_iff hN hq hd).mpr hdiv
  obtain ⟨hx, hqx, hy⟩ := low_scale_table_domain hN hq
  have hl := original_seed_low_lambda hN hd.2.2.2.2.le
  exact real_actual_zero_repulsion hx hqx (inducedAt d q) psi
    (by simpa only [hy] using he) (by simpa only [hy] using hz)
    (paper_induced_inverse d hdiv) hd.2.2.1 hret (by linarith)

theorem paper_source_retained_closed_cap_empty {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) (psi : Character q) :
    (retainedValues psi (omegaCutoff N q) d e).filter
      (fun rho => cap N 0.3221 ≤ rho.re) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro rho hr
  obtain ⟨hr, hcap⟩ := Finset.mem_filter.mp hr
  exact (not_lt_of_ge hcap) (paper_source_retained_strict hN hq hd hdiv psi hr)

end LiuWang.Proof.SourceRoute.Exception
