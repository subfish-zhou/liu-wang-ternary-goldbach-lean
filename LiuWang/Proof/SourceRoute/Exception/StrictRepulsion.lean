import LiuWang.Proof.MultiZeroRepulsion.Continuation.StrictTable
import LiuWang.Proof.WeightedLowZeros.Continuation.SourceComparison

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.Exception

theorem low_scale_table_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    8000000000 ≤ lowScale N ∧ (q : ℝ) ≤ lowScale N ∧
      lowScale N / q = omegaCutoff N q := by
  have hL := sourceL_ge_3100 hN
  have hP : (3100 : ℝ) ^ 3 ≤ sourceP N :=
    pow_le_pow_left₀ (by norm_num) hL 3
  have h := lowScale_parameters hN hq
  exact ⟨by dsimp [lowScale]; nlinarith, h.2⟩

def actualZeroSlot {q : ℕ} [NeZero q] (chi : Character q) {rho : ℂ} {y : ℝ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi y) : ZeroSlots q 0 y where
  character := chi
  value := rho
  index := 0
  zero_mem := by
    obtain ⟨hz, h0, h1, ht, _⟩ := CompleteExpansion.mem_zeroValues.mp hr
    exact mem_strictZeroValues.mpr ⟨hz, h0, h0, h1, ht⟩
  index_lt := by
    obtain ⟨hz, _, h1, _, _⟩ := CompleteExpansion.mem_zeroValues.mp hr
    exact ordinary_zero_order_pos chi (fun he => by simp [he] at h1) hz

theorem actual_zero_repulsion {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi psi : Character q) {e rho : ℂ}
    (he : e ∈ CompleteExpansion.zeroValues chi (x / q))
    (hr : rho ∈ CompleteExpansion.zeroValues psi (x / q))
    (hne : psi ≠ chi ∨ rho ≠ e)
    (hnc : psi ≠ chi⁻¹ ∨ rho ≠ conj e)
    (hl : (1 - e.re) * Real.log x ≤ 0.12) :
    rho.re < 1 - 0.3221 / Real.log x := by
  let p := actualZeroSlot chi he
  let r := actualZeroSlot psi hr
  have hpr : p ≠ r := by
    intro h
    exact hne.elim
      (fun hc => hc (congrArg ZeroSlots.character h).symm)
      (fun hv => hv (congrArg ZeroSlots.value h).symm)
  have hpc : p ≠ conjugateSlot r := by
    intro h
    have hc := congrArg ZeroSlots.character h
    have hv := congrArg ZeroSlots.value h
    change chi = psi⁻¹ at hc
    change e = conj rho at hv
    exact hnc.elim
      (fun hn => hn (by rw [hc, inv_inv]))
      (fun hn => hn (by rw [hv, Complex.conj_conj]))
  have h := ParentStrictTable.full_strip_strict .r12 hx hq p r hpr hpc
    (by norm_num [generalTableFirst, p, actualZeroSlot] at hl ⊢; exact hl)
  have h' : (0.3221 : ℝ) < (1 - rho.re) * Real.log x := by
    simpa only [generalTableSecond, r, actualZeroSlot, show (3221 / 10000 : ℝ) = 0.3221 by norm_num] using h
  have hlog : 0 < Real.log x := by linarith [source_log_lower hx]
  have hh := (div_lt_iff₀ hlog).mpr h'
  linarith

theorem real_actual_zero_repulsion {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi psi : Character q) {e rho : ℂ}
    (he : e ∈ CompleteExpansion.zeroValues chi (x / q))
    (hr : rho ∈ CompleteExpansion.zeroValues psi (x / q))
    (hc : chi⁻¹ = chi) (hi : e.im = 0)
    (hne : psi ≠ chi ∨ rho ≠ e)
    (hl : (1 - e.re) * Real.log x ≤ 0.12) :
    rho.re < 1 - 0.3221 / Real.log x := by
  have hec : conj e = e := by apply Complex.ext <;> simp [hi]
  exact actual_zero_repulsion hx hq chi psi he hr hne
    (by simpa only [hc, hec] using hne) hl

end LiuWang.Proof.SourceRoute.Exception
