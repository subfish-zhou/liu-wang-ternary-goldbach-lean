import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.PolynomialCost
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.ConductorMoments

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

def firstMomentBudget (N r : ℕ) : ℝ :=
  8.2e-10*(48.4*(r:ℝ)^(1/6:ℝ)/(r.totient:ℝ)^2) +
    (0.063/sourceL N^3)*(132*(r:ℝ)/(r.totient:ℝ)^2*sourceP N^(1/6:ℝ))

def secondMomentBudget (N r : ℕ) : ℝ :=
  (8.2e-10:ℝ)^2*(55*(r:ℝ)^(1/3:ℝ)/(r.totient:ℝ)^2) +
    (2*8.2e-10*0.063/sourceL N^3)*(66*(r:ℝ)/(r.totient:ℝ)^2*sourceP N^(1/3:ℝ)) +
    (0.063^2/sourceL N^6)*(22*(r:ℝ)/(r.totient:ℝ)^2*sourceP N^(4/3:ℝ))

def analyticCost (N r : ℕ) (beta : ℝ) : MixedKind → ℝ
  | .oneEach => 3.6*Real.sqrt r*baseWeight N beta*(N:ℝ)^2*firstMomentBudget N r
  | .oneExceptionalTwoRegular =>
      1.08*Real.sqrt r*baseWeight N beta*(N:ℝ)^2*secondMomentBudget N r
  | .twoExceptionalOneRegular => 1.8*r*baseWeight N beta^2*(N:ℝ)^2*firstMomentBudget N r

theorem firstPolynomial_sum (N r : ℕ) :
    (∑ q ∈ denominators (sourceP N), if r ∣ q then
      firstPolynomial N q/(q.totient:ℝ)^2 else 0) =
      8.2e-10*multipleMoment (sourceP N) r (1/6) +
        (0.063/sourceL N^3)*multipleMoment (sourceP N) r (7/6) := by
  simp only [multipleMoment, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  split_ifs
  · unfold firstPolynomial
    ring
  · ring

theorem secondPolynomial_sum (N r : ℕ) :
    (∑ q ∈ denominators (sourceP N), if r ∣ q then
      secondPolynomial N q/(q.totient:ℝ)^2 else 0) =
      (8.2e-10:ℝ)^2*multipleMoment (sourceP N) r (1/3) +
        (2*8.2e-10*0.063/sourceL N^3)*multipleMoment (sourceP N) r (4/3) +
        (0.063^2/sourceL N^6)*multipleMoment (sourceP N) r (7/3) := by
  simp only [multipleMoment, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  split_ifs
  · unfold secondPolynomial
    ring
  · ring

theorem firstPolynomial_sum_le {N r : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hr : 0 < r) :
    (∑ q ∈ denominators (sourceP N), if r ∣ q then
      firstPolynomial N q/(q.totient:ℝ)^2 else 0) ≤ firstMomentBudget N r := by
  rw [firstPolynomial_sum]
  have h := original_five_moments (sourceP_pos hN).le hr
  have hl := sourceL_pos hN
  unfold firstMomentBudget
  exact add_le_add (mul_le_mul_of_nonneg_left h.1 (by norm_num))
    (mul_le_mul_of_nonneg_left h.2.1 (by positivity))

theorem secondPolynomial_sum_le {N r : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hr : 0 < r) :
    (∑ q ∈ denominators (sourceP N), if r ∣ q then
      secondPolynomial N q/(q.totient:ℝ)^2 else 0) ≤ secondMomentBudget N r := by
  rw [secondPolynomial_sum]
  have h := original_five_moments (sourceP_pos hN).le hr
  have hl := sourceL_pos hN
  unfold secondMomentBudget
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h.2.2.1 (by norm_num))
    (mul_le_mul_of_nonneg_left h.2.2.2.1 (by positivity)))
    (mul_le_mul_of_nonneg_left h.2.2.2.2 (by positivity))

theorem normalizedTotal_le_analytic {N r : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hr : 0 < r) (beta : ℝ) (j : MixedKind) :
    normalizedTotal N r beta j ≤ analyticCost N r beta j := by
  have h : normalizedTotal N r beta j ≤ ∑ q ∈ denominators (sourceP N),
      if r ∣ q then polynomialCost N q r beta j else 0 := by
    apply sum_le_sum
    intro q hq
    split_ifs
    · exact normalizedCost_le_polynomial hN (mem_Icc.mp hq).1 beta j
    · rfl
  have hs (f : ℕ → ℝ) (C : ℝ) :
      (∑ q ∈ denominators (sourceP N), if r ∣ q then C*f q else 0) =
        C*∑ q ∈ denominators (sourceP N), if r ∣ q then f q else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro q _
    split_ifs <;> ring
  have hb : 0 ≤ baseWeight N beta := by unfold baseWeight; positivity
  cases j <;> simp only [polynomialCost, hs] at h <;> apply h.trans
  · exact mul_le_mul_of_nonneg_left (firstPolynomial_sum_le hN hr) (by positivity)
  · exact mul_le_mul_of_nonneg_left (secondPolynomial_sum_le hN hr) (by positivity)
  · exact mul_le_mul_of_nonneg_left (firstPolynomial_sum_le hN hr) (by positivity)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
