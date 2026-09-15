import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorConjugation
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
Analytic soundness of critical-line sign certificates for the actual completed
zeta function. No sign evaluations or completeness counts are supplied here.
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def criticalPoint (t : ℝ) : ℂ := ⟨1 / 2, t⟩

def criticalCompletedZeta (t : ℝ) : ℝ :=
  (completedRiemannZeta (criticalPoint t)).re

theorem criticalPoint_ne_zero (t : ℝ) : criticalPoint t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [criticalPoint] at this

theorem criticalPoint_ne_one (t : ℝ) : criticalPoint t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num [criticalPoint] at this

theorem completedZeta_conj_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  have hsc0 : conj s ≠ 0 := by simpa using hs0
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hGc := Complex.Gammaℝ_ne_zero_of_re_pos (s := conj s) (by simpa using hs)
  have hz := (eq_div_iff hG).mp (riemannZeta_def_of_ne_zero hs0)
  have hzc := (eq_div_iff hGc).mp (riemannZeta_def_of_ne_zero hsc0)
  rw [← hzc, ← hz, riemannZeta_conj,
    BombieriVinogradov.SiegelWalfisz.Complex.Gammaℝ_conj, map_mul]

theorem criticalCompletedZeta_ofReal (t : ℝ) :
    (criticalCompletedZeta t : ℂ) = completedRiemannZeta (criticalPoint t) := by
  have hp : conj (criticalPoint t) = 1 - criticalPoint t := by
    apply Complex.ext <;> norm_num [criticalPoint]
  have hc : conj (completedRiemannZeta (criticalPoint t)) =
      completedRiemannZeta (criticalPoint t) := by
    rw [← completedZeta_conj_of_re_pos (by norm_num [criticalPoint] :
      0 < (criticalPoint t).re), hp, completedRiemannZeta_one_sub]
  apply Complex.ext
  · rfl
  · simpa using (Complex.conj_eq_iff_im.mp hc).symm

theorem criticalCompletedZeta_eq_zero_iff (t : ℝ) :
    criticalCompletedZeta t = 0 ↔ riemannZeta (criticalPoint t) = 0 := by
  rw [riemannZeta_def_of_ne_zero (criticalPoint_ne_zero t),
    div_eq_zero_iff, or_iff_left (Complex.Gammaℝ_ne_zero_of_re_pos
      (by norm_num [criticalPoint] : 0 < (criticalPoint t).re))]
  rw [← criticalCompletedZeta_ofReal]
  exact Complex.ofReal_eq_zero.symm

theorem continuous_criticalCompletedZeta : Continuous criticalCompletedZeta := by
  have hp : Continuous criticalPoint := by
    have he : criticalPoint = (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) := by
      funext t
      apply Complex.ext <;> simp [criticalPoint]
    rw [he]
    fun_prop
  have hc : Continuous (fun t : ℝ => completedRiemannZeta (criticalPoint t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (differentiableAt_completedZeta (criticalPoint_ne_zero t)
      (criticalPoint_ne_one t)).continuousAt.comp hp.continuousAt
  exact Complex.continuous_re.comp hc

theorem exists_critical_zero_of_sign_change {a b : ℝ} (hab : a < b)
    (hsign : criticalCompletedZeta a * criticalCompletedZeta b < 0) :
    ∃ t ∈ Ioo a b, riemannZeta (criticalPoint t) = 0 := by
  have hcont := continuous_criticalCompletedZeta.continuousOn (s := Icc a b)
  have hw : ∃ t ∈ Icc a b, criticalCompletedZeta t = 0 := by
    rcases mul_neg_iff.mp hsign with h | h
    · exact intermediate_value_Icc' hab.le hcont ⟨h.2.le, h.1.le⟩
    · exact intermediate_value_Icc hab.le hcont ⟨h.1.le, h.2.le⟩
  obtain ⟨t, ht, hz⟩ := hw
  have hta : t ≠ a := by
    intro h
    subst t
    rw [hz, zero_mul] at hsign
    exact (lt_irrefl 0) hsign
  have htb : t ≠ b := by
    intro h
    subst t
    rw [hz, mul_zero] at hsign
    exact (lt_irrefl 0) hsign
  exact ⟨t, ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩,
    (criticalCompletedZeta_eq_zero_iff t).mp hz⟩

#print axioms completedZeta_conj_of_re_pos
#print axioms criticalCompletedZeta_ofReal
#print axioms criticalCompletedZeta_eq_zero_iff
#print axioms continuous_criticalCompletedZeta
#print axioms exists_critical_zero_of_sign_change

end LiuWang.Proof.Campaign20260915.ZetaValidation
