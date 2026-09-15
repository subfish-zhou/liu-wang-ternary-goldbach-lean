import LiuWang.Proof.Campaign20260915.ZetaWinding.HorizontalCount
import LiuWang.Proof.DirichletZeroCount.Applications.RightLimit
import BombieriVinogradov.Helpers.ComplexAnalysis.AnalyticOrderConjugation

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.DirichletZeroCount

def positiveValues (T : ℝ) : Finset ℂ :=
  (zetaClosedValues T).filter (fun z => 0 < z.im)

def positiveCount (T : ℝ) : ℕ :=
  ∑ z ∈ positiveValues T, analyticOrderNatAt riemannZeta z

def positiveCountLeft (T : ℝ) : ℕ :=
  ∑ z ∈ (positiveValues T).filter (fun z => z.im < T),
    analyticOrderNatAt riemannZeta z

def boundaryMultiplicity (T : ℝ) : ℕ :=
  ∑ z ∈ (positiveValues T).filter (fun z => z.im = T),
    analyticOrderNatAt riemannZeta z

theorem mem_positiveValues {T : ℝ} {z : ℂ} :
    z ∈ positiveValues T ↔
      riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im ≤ T := by
  simp only [positiveValues, Finset.mem_filter, mem_zetaClosedValues]
  constructor
  · rintro ⟨⟨hz, h0, h1, ht⟩, hp⟩
    exact ⟨hz, h0, h1, hp, (le_abs_self _).trans ht⟩
  · rintro ⟨hz, h0, h1, hp, ht⟩
    exact ⟨⟨hz, h0, h1, by rwa [abs_of_pos hp]⟩, hp⟩

theorem zeta_order_conj {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderNatAt riemannZeta (conj z) = analyticOrderNatAt riemannZeta z := by
  have hn : z ≠ 1 := by intro he; simp [he] at h1
  have hcn : conj z ≠ 1 := by intro he; apply hn; simpa using congrArg conj he
  have h := BombieriVinogradov.ComplexAnalysis.AnalyticAt.analyticOrderNatAt_conj_conj
    (f := riemannXi) (z := conj z) (differentiable_riemannXi.analyticAt _)
  have hf : (fun w => conj (riemannXi (conj w))) = riemannXi := by
    funext w
    rw [Argument.xi_conjugate, Complex.conj_conj]
  rw [hf] at h
  simp only [Complex.conj_conj] at h
  have he := LiuWang.Proof.PrincipalPsi.Quantitative.analyticOrderNatAt_xi_eq_principal
    (q := 1) h0 hn
  have hec := LiuWang.Proof.PrincipalPsi.Quantitative.analyticOrderNatAt_xi_eq_principal
    (q := 1) (s := conj z) (by simpa using h0) hcn
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hec.symm.trans (h.trans he)

theorem zetaClosedCount_eq_two_positiveCount (T : ℝ) :
    zetaClosedCount T = 2 * positiveCount T := by
  classical
  let negs := (zetaClosedValues T).filter (fun z => ¬ 0 < z.im)
  have hc : ∑ z ∈ negs, analyticOrderNatAt riemannZeta z = positiveCount T := by
    apply Finset.sum_bij (fun z _ => conj z)
    · intro z hz
      obtain ⟨hm, hn⟩ := Finset.mem_filter.mp hz
      obtain ⟨hz, h0, h1, ht⟩ := mem_zetaClosedValues.mp hm
      have hi : z.im < 0 := by
        have hi0 : z.im ≠ 0 := by
          intro he
          exact zeta_ne_zero_closed_height_one h0 h1 (by simp [he]) hz
        exact lt_of_le_of_ne (not_lt.mp hn) hi0
      apply mem_positiveValues.mpr
      exact ⟨by rw [riemannZeta_conj, hz, map_zero],
        by simpa using h0, by simpa using h1, by simpa using neg_pos.mpr hi,
        by simpa [abs_of_neg hi] using ht⟩
    · intro z _ w _ he
      simpa using congrArg conj he
    · intro z hz
      obtain ⟨hz, h0, h1, hp, ht⟩ := mem_positiveValues.mp hz
      refine ⟨conj z, ?_, by simp⟩
      apply Finset.mem_filter.mpr
      refine ⟨mem_zetaClosedValues.mpr ?_, by simpa using (not_lt.mpr hp.le)⟩
      exact ⟨by rw [riemannZeta_conj, hz, map_zero],
        by simpa using h0, by simpa using h1, by simpa [abs_of_pos hp] using ht⟩
    · intro z hz
      have hm := mem_zetaClosedValues.mp (Finset.mem_filter.mp hz).1
      exact (zeta_order_conj hm.2.1 hm.2.2.1).symm
  have hs := Finset.sum_filter_add_sum_filter_not (zetaClosedValues T)
    (fun z : ℂ => 0 < z.im) (analyticOrderNatAt riemannZeta)
  change positiveCount T + (∑ z ∈ negs, analyticOrderNatAt riemannZeta z) =
    zetaClosedCount T at hs
  rw [hc] at hs
  omega

theorem positiveCount_jump (T : ℝ) :
    positiveCount T = positiveCountLeft T + boundaryMultiplicity T := by
  classical
  have hs := Finset.sum_filter_add_sum_filter_not (positiveValues T)
    (fun z : ℂ => z.im < T) (analyticOrderNatAt riemannZeta)
  have he : (positiveValues T).filter (fun z => ¬ z.im < T) =
      (positiveValues T).filter (fun z => z.im = T) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hn⟩
      exact ⟨hz, le_antisymm (mem_positiveValues.mp hz).2.2.2.2 (not_lt.mp hn)⟩
    · rintro ⟨hz, he⟩
      exact ⟨hz, by rw [he]; exact lt_irrefl T⟩
  rw [he] at hs
  exact hs.symm

theorem positiveCount_mono : Monotone positiveCount := by
  intro a b hab
  have ha := zetaClosedCount_eq_two_positiveCount a
  have hb := zetaClosedCount_eq_two_positiveCount b
  have hm := count_mono_height (1 : LiuWang.Proof.Interfaces.Character 1) 0 hab
  rw [← zetaClosedCount_eq_principal, ← zetaClosedCount_eq_principal, ha, hb] at hm
  omega

theorem positiveCount_right_continuous (T : ℝ) :
    ContinuousWithinAt (fun t => (positiveCount t : ℝ)) (Set.Ici T) T := by
  have he (t : ℝ) : (positiveCount t : ℝ) = (zetaClosedCount t : ℝ) / 2 := by
    rw [zetaClosedCount_eq_two_positiveCount]
    push_cast
    ring
  simp_rw [he, zetaClosedCount_eq_principal]
  exact (Applications.count_continuousWithinAt_right
    (1 : LiuWang.Proof.Interfaces.Character 1) 0 T).div_const 2

theorem positiveCount_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t => (positiveCount t : ℝ)) volume a b :=
  (show Monotone (fun t => (positiveCount t : ℝ)) from
    fun _ _ h => Nat.cast_le.mpr (positiveCount_mono h)).intervalIntegrable

theorem positiveCount_sixteen : positiveCount 16 = 1 := by
  have h := zetaClosedCount_eq_two_positiveCount 16
  rw [zetaClosedCount_sixteen] at h
  omega

#print axioms zetaClosedCount_eq_two_positiveCount
#print axioms positiveCount_jump
#print axioms positiveCount_right_continuous
#print axioms positiveCount_intervalIntegrable

end LiuWang.Proof.Campaign20260915.ZetaWinding
