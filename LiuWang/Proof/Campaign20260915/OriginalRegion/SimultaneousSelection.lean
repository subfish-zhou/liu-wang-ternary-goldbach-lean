import LiuWang.Proof.Campaign20260915.OriginalRegion.BranchSelections
import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Pole

/-! Separate low-order selections pay the actual moving poles without a debit per zero. -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open scoped Classical BigOperators ComplexConjugate
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.Uniform
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem lecture_center_selected {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : 1 / 2 < rho.re ∧ rho.re < 1) (hz : chi.LFunction rho = 0)
    {sigma : ℝ} (hs : 1 < sigma) :
    19.073344004352 * reflectedKernel sigma rho.im rho ≤
      ∑ j : Fin 5, lectureCoefficients j * signedCost (chi ^ (j : ℕ)) sigma ((j : ℝ) * rho.im) := by
  have hh := lecture_selected_bound chi hs rho.im
    (![∅, {rho}, ∅, ∅, ∅] : Fin 5 → Finset ℂ) (by
      intro j tau ht
      fin_cases j <;> simp_all)
  norm_num [Fin.sum_univ_succ, lectureCoefficients_exact, ordinaryMass] at hh ⊢
  have hm := reflectedKernel_le_singleton_mass chi hs rho.im ⟨by linarith [hr.1], hr.2⟩ hz
  simp only [ordinaryMass, Finset.sum_singleton] at hm
  linarith

theorem cubic_lecture_poles_paid {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (h3 : chi ^ 3 = 1)
    {rho : ℂ} (hr : 9 / 10 ≤ rho.re) (hr1 : rho.re < 1) (hz : chi.LFunction rho = 0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50)
    (hgap : 1 - rho.re ≤ sigma - 1) :
    19.073344004352 * reflectedKernel sigma rho.im rho +
      4.7568 * poleDifference sigma (3 * rho.im) ≤
      ∑ j : Fin 5, lectureCoefficients j * signedCost (chi ^ (j : ℕ)) sigma ((j : ℝ) * rho.im) := by
  have hz' : chi⁻¹.LFunction (conj rho) = 0 := by
    rw [DirichletCharacter.LFunction_inv_eq_conj_conj hc, conj_conj, hz, map_zero]
  have hsel := cubic_lecture_selected chi h3 ⟨by linarith, hr1⟩ hs
  have h1 := reflectedKernel_le_singleton_mass chi hs rho.im ⟨by linarith, hr1⟩ hz
  have h2 := reflectedKernel_le_singleton_mass chi⁻¹ hs (2 * rho.im)
    (rho := conj rho) ⟨by simpa using (show 0 < rho.re by linarith), by simpa using hr1⟩ hz'
  have h4 := reflectedKernel_le_singleton_mass chi hs (4 * rho.im) ⟨by linarith, hr1⟩ hz
  have hp := t1_two_kernels_pay_pole hs hs1
    (rho := conj rho) (tau := conj rho) (t := 2 * rho.im) (u := 2 * rho.im)
    (v := 3 * rho.im) (by simpa using hr) (by simpa using hr1)
    (by simpa using hr) (by simpa using hr1)
    (by simpa using hgap) (by simpa using hgap)
    (by simp [conj_im]; ring) (by simp [conj_im]; ring)
  have hn2 := dampedZeroKernel_pair_nonneg hs (2 * rho.im)
    (rho := conj rho) ⟨by simpa using (show 0 ≤ rho.re by linarith), by simpa using hr1.le⟩
  have hn4 := dampedZeroKernel_pair_nonneg hs (4 * rho.im)
    (rho := rho) ⟨by linarith, hr1.le⟩
  change 0 ≤ reflectedKernel sigma (2 * rho.im) (conj rho) at hn2
  change 0 ≤ reflectedKernel sigma (4 * rho.im) rho at hn4
  linarith

theorem fourth_lecture_poles_paid {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (h4 : chi ^ 4 = 1)
    {rho : ℂ} (hr : 9 / 10 ≤ rho.re) (hr1 : rho.re < 1) (hz : chi.LFunction rho = 0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50)
    (hgap : 1 - rho.re ≤ sigma - 1) :
    19.073344004352 * reflectedKernel sigma rho.im rho +
      poleDifference sigma (4 * rho.im) ≤
      ∑ j : Fin 5, lectureCoefficients j * signedCost (chi ^ (j : ℕ)) sigma ((j : ℝ) * rho.im) := by
  have hz' : chi⁻¹.LFunction (conj rho) = 0 := by
    rw [DirichletCharacter.LFunction_inv_eq_conj_conj hc, conj_conj, hz, map_zero]
  have hsel := fourth_lecture_selected chi h4 ⟨by linarith, hr1⟩ hs
  have h1 := reflectedKernel_le_singleton_mass chi hs rho.im ⟨by linarith, hr1⟩ hz
  have h3 := reflectedKernel_le_singleton_mass chi⁻¹ hs (3 * rho.im)
    (rho := conj rho) ⟨by simpa using (show 0 < rho.re by linarith), by simpa using hr1⟩ hz'
  have hp := t1_two_kernels_pay_pole hs hs1
    (rho := conj rho) (tau := conj rho) (t := 3 * rho.im) (u := 3 * rho.im)
    (v := 4 * rho.im) (by simpa using hr) (by simpa using hr1)
    (by simpa using hr) (by simpa using hr1)
    (by simpa using hgap) (by simpa using hgap)
    (by simp [conj_im]; ring) (by simp [conj_im]; ring)
  have hn := dampedZeroKernel_pair_nonneg hs (3 * rho.im)
    (rho := conj rho) ⟨by simpa using (show 0 ≤ rho.re by linarith), by simpa using hr1.le⟩
  change 0 ≤ reflectedKernel sigma (3 * rho.im) (conj rho) at hn
  linarith

theorem quadratic_lecture_poles_paid {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (h2 : chi ^ 2 = 1)
    {rho : ℂ} (hr : 9 / 10 ≤ rho.re) (hr1 : rho.re < 1) (hz : chi.LFunction rho = 0)
    (hi : rho.im ≠ 0) {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50)
    (hgap : 1 - rho.re ≤ sigma - 1) :
    19.073344004352 * reflectedKernel sigma rho.im rho +
      11.67618784 * poleDifference sigma (2 * rho.im) +
      poleDifference sigma (4 * rho.im) ≤
      ∑ j : Fin 5, lectureCoefficients j * signedCost (chi ^ (j : ℕ)) sigma ((j : ℝ) * rho.im) := by
  have hinv : chi⁻¹ = chi := (power_predecessor_eq_inverse (j := 1) h2).symm.trans (pow_one chi)
  have hz' : chi.LFunction (conj rho) = 0 := by
    rw [← hinv, DirichletCharacter.LFunction_inv_eq_conj_conj hc, conj_conj, hz, map_zero]
  have hne : rho ≠ conj rho := by
    intro he
    have hh := congrArg Complex.im he
    simp only [conj_im] at hh
    exact hi (by linarith)
  have hm (t : ℝ) : reflectedKernel sigma t rho + reflectedKernel sigma t (conj rho) ≤
      ordinaryMass chi sigma t {rho, conj rho} := by
    have h1 := reflectedKernel_le_singleton_mass chi hs t ⟨by linarith, hr1⟩ hz
    have h2 := reflectedKernel_le_singleton_mass chi hs t (rho := conj rho)
      ⟨by simpa using (show 0 < rho.re by linarith), by simpa using hr1⟩ hz'
    simp only [ordinaryMass, Finset.sum_singleton, Finset.sum_pair hne] at *
    linarith
  have hsel := lecture_selected_bound chi hs rho.im
    (![∅, {rho, conj rho}, ∅, {rho, conj rho}, ∅] : Fin 5 → Finset ℂ) (by
      intro j tau ht
      fin_cases j <;> simp_all <;>
        rcases ht with rfl | rfl <;> constructor <;> norm_num only [conj_re] <;> linarith)
  have h3 : chi ^ 3 = chi := by rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, h2, one_mul]
  norm_num [Fin.sum_univ_succ, lectureCoefficients_exact, h3, ordinaryMass] at hsel ⊢
  have he : reflectedKernel sigma (3 * rho.im) rho = reflectedKernel sigma rho.im (conj rho) := by
    simp only [reflectedKernel_eq_rational, conj_re, conj_im]
    congr 2 <;> ring
  have hp2 := t1_two_kernels_pay_pole hs hs1
    (rho := conj rho) (tau := conj rho) (t := rho.im) (u := rho.im)
    (v := 2 * rho.im) (by simpa using hr) (by simpa using hr1)
    (by simpa using hr) (by simpa using hr1)
    (by simpa using hgap) (by simpa using hgap)
    (by simp [conj_im]; ring) (by simp [conj_im]; ring)
  have hp4 := t1_two_kernels_pay_pole hs hs1
    (rho := conj rho) (tau := conj rho) (t := 3 * rho.im) (u := 3 * rho.im)
    (v := 4 * rho.im) (by simpa using hr) (by simpa using hr1)
    (by simpa using hr) (by simpa using hr1)
    (by simpa using hgap) (by simpa using hgap)
    (by simp [conj_im]; ring) (by simp [conj_im]; ring)
  have hm1 := hm rho.im
  have hm3 := hm (3 * rho.im)
  rw [he] at hm3
  simp only [ordinaryMass, Finset.sum_pair hne, he] at hm1 hm3 hsel
  have hn2 := dampedZeroKernel_pair_nonneg hs rho.im
    (rho := conj rho) ⟨by simpa using (show 0 ≤ rho.re by linarith), by simpa using hr1.le⟩
  have hn4 := dampedZeroKernel_pair_nonneg hs (3 * rho.im)
    (rho := conj rho) ⟨by simpa using (show 0 ≤ rho.re by linarith), by simpa using hr1.le⟩
  change 0 ≤ reflectedKernel sigma rho.im (conj rho) at hn2
  change 0 ≤ reflectedKernel sigma (3 * rho.im) (conj rho) at hn4
  linarith

theorem all_nonprincipal_lecture_poles_paid {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : 9 / 10 ≤ rho.re) (hr1 : rho.re < 1) (hz : chi.LFunction rho = 0)
    (hbranch : chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50) (hgap : 1 - rho.re ≤ sigma - 1) :
    19.073344004352 * reflectedKernel sigma rho.im rho +
      11.67618784 * harmonicPole (chi ^ 2) sigma (2 * rho.im) +
      4.7568 * harmonicPole (chi ^ 3) sigma (3 * rho.im) +
      harmonicPole (chi ^ 4) sigma (4 * rho.im) ≤
      ∑ j : Fin 5, lectureCoefficients j * signedCost (chi ^ (j : ℕ)) sigma ((j : ℝ) * rho.im) := by
  by_cases h2 : chi ^ 2 = 1
  · have h3 : chi ^ 3 = chi := by rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, h2, one_mul]
    have h4 : chi ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, h2, one_pow]
    have hi := hbranch.resolve_left (not_ne_iff.mpr h2)
    simpa only [harmonicPole, h2, h3, h4, ite_true, if_neg hc, mul_zero, add_zero] using
      quadratic_lecture_poles_paid chi hc h2 hr hr1 hz hi hs hs1 hgap
  · by_cases h3 : chi ^ 3 = 1
    · have h4 : chi ^ 4 = chi := by rw [show (4 : ℕ) = 3 + 1 by rfl, pow_succ, h3, one_mul]
      simpa only [harmonicPole, h3, h4, ite_true, if_neg hc, if_neg h2, mul_zero, add_zero] using
        cubic_lecture_poles_paid chi hc h3 hr hr1 hz hs hs1 hgap
    · by_cases h4 : chi ^ 4 = 1
      · simpa only [harmonicPole, h4, ite_true, if_neg h2, if_neg h3, mul_zero, add_zero] using
          fourth_lecture_poles_paid chi hc h4 hr hr1 hz hs hs1 hgap
      · simpa only [harmonicPole, if_neg h2, if_neg h3, if_neg h4, mul_zero, add_zero] using
          lecture_center_selected chi ⟨by linarith, hr1⟩ hz hs

end LiuWang.Proof.Campaign20260915.OriginalRegion
