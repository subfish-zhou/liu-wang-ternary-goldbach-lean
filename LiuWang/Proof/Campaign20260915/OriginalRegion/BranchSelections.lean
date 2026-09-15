import LiuWang.Proof.Campaign20260915.OriginalRegion.LecturePolynomial
import LiuWang.Proof.MultiZeroRepulsion.ConjugateSlots
import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.Inverse

/-! Actual extra selections for low-order characters; conjugate points are not merged. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators Classical ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem reflectedKernel_conjugate_at_zero (sigma : ℝ) (rho : ℂ) :
    reflectedKernel sigma 0 (conj rho) = reflectedKernel sigma 0 rho := by
  simp only [reflectedKernel_eq_rational, conj_re, conj_im, zero_sub, neg_neg, neg_sq]

theorem quadratic_conjugate_mass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (h2 : chi ^ 2 = 1) {rho : ℂ}
    (hr : rho.re ∈ Set.Ioo (0 : ℝ) 1) (hi : rho.im ≠ 0) (sigma : ℝ) :
    ordinaryMass chi sigma 0 {rho, conj rho} =
      2 * (analyticOrderNatAt chi.LFunction rho : ℝ) * reflectedKernel sigma 0 rho := by
  have hinv : chi⁻¹ = chi := (power_predecessor_eq_inverse (j := 1) h2).symm.trans (pow_one chi)
  have hm := ordinary_order_conjugate chi hr.1 hr.2
  rw [hinv] at hm
  have hne : rho ≠ conj rho := by
    intro he
    have hh := congrArg Complex.im he
    simp only [conj_im] at hh
    exact hi (by linarith)
  simp only [ordinaryMass, Finset.sum_pair hne, hm, reflectedKernel_conjugate_at_zero]
  ring

theorem real_axis_signed_selection {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ}
    (hs : 1 < sigma) (v : Finset ℂ)
    (hr : ∀ rho ∈ v, 1 / 2 < rho.re ∧ rho.re < 1) :
    ordinaryMass chi sigma 0 v ≤
      signedCost (1 : DirichletCharacter ℂ q) sigma 0 + signedCost chi sigma 0 := by
  have hp (n : ℕ) (hn : n ≠ 0) (hu : IsUnit (n : ZMod q)) :
      0 ≤ ∑ j : Fin 2, (1 : ℝ) *
        (phase ((![1, chi] : Fin 2 → DirichletCharacter ℂ q) j) 0 n).re := by
    have hh := (neg_le_abs (phase chi 0 n).re).trans (abs_re_le_norm _)
    rw [phase_norm chi hn hu] at hh
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, one_mul, phase_one hu, one_re]
    linarith
  have hh := signed_polynomial_selected_bound Finset.univ
    (![1, chi] : Fin 2 → DirichletCharacter ℂ q) (fun _ => 0) (fun _ => 1)
    (by intros; norm_num) hp hs (![∅, v] : Fin 2 → Finset ℂ) (by
      intro j _ rho h
      fin_cases j
      · simp at h
      · exact hr rho h)
  simpa [Fin.sum_univ_succ, ordinaryMass] using hh

theorem quadratic_pair_signed_budget {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (h2 : chi ^ 2 = 1) {rho : ℂ}
    (hr : 1 / 2 < rho.re ∧ rho.re < 1) (hi : rho.im ≠ 0)
    {sigma : ℝ} (hs : 1 < sigma) :
    2 * (analyticOrderNatAt chi.LFunction rho : ℝ) * reflectedKernel sigma 0 rho ≤
      signedCost (1 : DirichletCharacter ℂ q) sigma 0 + signedCost chi sigma 0 := by
  rw [← quadratic_conjugate_mass chi h2 ⟨by linarith [hr.1], hr.2⟩ hi sigma]
  exact real_axis_signed_selection chi hs _ (by simpa using And.intro hr hr)

theorem cubic_lecture_selected {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (h3 : chi ^ 3 = 1) {rho : ℂ}
    (hr : 1 / 2 < rho.re ∧ rho.re < 1) {sigma : ℝ} (hs : 1 < sigma) :
    19.073344004352 * ordinaryMass chi sigma rho.im {rho} +
      11.67618784 * ordinaryMass chi⁻¹ sigma (2 * rho.im) {conj rho} +
      ordinaryMass chi sigma (4 * rho.im) {rho} ≤
      ∑ j : Fin 5, lectureCoefficients j * signedCost (chi ^ (j : ℕ)) sigma ((j : ℝ) * rho.im) := by
  have hh := lecture_selected_bound chi hs rho.im
    (![∅, {rho}, {conj rho}, ∅, {rho}] : Fin 5 → Finset ℂ) (by
      intro j tau ht
      fin_cases j <;> simp_all)
  have h2 := power_predecessor_eq_inverse (j := 2) h3
  have h4 : chi ^ 4 = chi := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, one_mul]
  have hl :
      (∑ j : Fin 5, lectureCoefficients j *
        ordinaryMass (chi ^ (j : ℕ)) sigma ((j : ℝ) * rho.im)
          ((![∅, {rho}, {conj rho}, ∅, {rho}] : Fin 5 → Finset ℂ) j)) =
        19.073344004352 * ordinaryMass chi sigma rho.im {rho} +
          11.67618784 * ordinaryMass chi⁻¹ sigma (2 * rho.im) {conj rho} +
          ordinaryMass chi sigma (4 * rho.im) {rho} := by
    norm_num [Fin.sum_univ_succ, lectureCoefficients_exact, h2, h4, ordinaryMass, add_assoc]
  rw [hl] at hh
  exact hh

theorem fourth_lecture_selected {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (h4 : chi ^ 4 = 1) {rho : ℂ}
    (hr : 1 / 2 < rho.re ∧ rho.re < 1) {sigma : ℝ} (hs : 1 < sigma) :
    19.073344004352 * ordinaryMass chi sigma rho.im {rho} +
      4.7568 * ordinaryMass chi⁻¹ sigma (3 * rho.im) {conj rho} ≤
      ∑ j : Fin 5, lectureCoefficients j * signedCost (chi ^ (j : ℕ)) sigma ((j : ℝ) * rho.im) := by
  have hh := lecture_selected_bound chi hs rho.im
    (![∅, {rho}, ∅, {conj rho}, ∅] : Fin 5 → Finset ℂ) (by
      intro j tau ht
      fin_cases j <;> simp_all)
  have h3 := power_predecessor_eq_inverse (j := 3) h4
  have hl :
      (∑ j : Fin 5, lectureCoefficients j *
        ordinaryMass (chi ^ (j : ℕ)) sigma ((j : ℝ) * rho.im)
          ((![∅, {rho}, ∅, {conj rho}, ∅] : Fin 5 → Finset ℂ) j)) =
        19.073344004352 * ordinaryMass chi sigma rho.im {rho} +
          4.7568 * ordinaryMass chi⁻¹ sigma (3 * rho.im) {conj rho} := by
    norm_num [Fin.sum_univ_succ, lectureCoefficients_exact, h3, ordinaryMass]
  rw [hl] at hh
  exact hh

end LiuWang.Proof.Campaign20260915.OriginalRegion
