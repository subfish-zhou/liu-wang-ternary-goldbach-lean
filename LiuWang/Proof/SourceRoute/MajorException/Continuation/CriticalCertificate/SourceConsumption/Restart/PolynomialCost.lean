import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.RadiusPayment
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.SourceTotal

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

def firstPolynomial (N q : ℕ) : ℝ :=
  8.2e-10*(q:ℝ)^(1/6:ℝ) + (0.063/sourceL N^3)*(q:ℝ)^(7/6:ℝ)

def secondPolynomial (N q : ℕ) : ℝ :=
  (8.2e-10:ℝ)^2*(q:ℝ)^(1/3:ℝ) +
    (2*8.2e-10*0.063/sourceL N^3)*(q:ℝ)^(4/3:ℝ) +
    (0.063^2/sourceL N^6)*(q:ℝ)^(7/3:ℝ)

theorem power_affine {x : ℝ} (hx : 0 < x) (s a b : ℝ) :
    x^s*(a+b*x) = a*x^s+b*x^(s+1) := by
  rw [Real.rpow_add hx, Real.rpow_one]
  ring

theorem power_affine_square {x : ℝ} (hx : 0 < x) (s a b : ℝ) :
    x^s*(a+b*x)^2 = a^2*x^s+2*a*b*x^(s+1)+b^2*x^(s+2) := by
  rw [Real.rpow_add hx, Real.rpow_one, Real.rpow_add hx, Real.rpow_two]
  ring

theorem firstPolynomial_nonneg {N : ℕ} (hN : Real.exp 2000 ≤ (N:ℝ)) (q : ℕ) :
    0 ≤ firstPolynomial N q := by
  have hl := sourceL_pos hN
  unfold firstPolynomial
  positivity

theorem secondPolynomial_nonneg {N : ℕ} (hN : Real.exp 2000 ≤ (N:ℝ)) (q : ℕ) :
    0 ≤ secondPolynomial N q := by
  have hl := sourceL_pos hN
  unfold secondPolynomial
  positivity

theorem firstPolynomial_scale {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hq : 0 < q) :
    Real.sqrt q * (radiusRoot N q * originalMotherBudget N q) ≤
      0.6*firstPolynomial N q := by
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  have he : Real.sqrt q*(q:ℝ)^(-(1:ℝ)/3) = (q:ℝ)^(1/6:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq0]
    norm_num
  apply (mul_le_mul_of_nonneg_left (root_times_originalMother hN hq)
    (Real.sqrt_nonneg _)).trans_eq
  rw [show Real.sqrt q*(0.6*(q:ℝ)^(-(1:ℝ)/3)*(8.2e-10+0.063*q/sourceL N^3)) =
    0.6*(Real.sqrt q*(q:ℝ)^(-(1:ℝ)/3))*(8.2e-10+(0.063/sourceL N^3)*q) by ring,
    he, mul_assoc, power_affine hq0]
  norm_num only [show (1/6:ℝ)+1=7/6 by norm_num]
  norm_num [firstPolynomial]

theorem secondPolynomial_scale {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hq : 0 < q) :
    (q:ℝ)*(radiusRoot N q*originalMotherBudget N q)^2 ≤ 0.36*secondPolynomial N q := by
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  have hh : 0 ≤ radiusRoot N q*originalMotherBudget N q :=
    mul_nonneg (roots_pos hN hq).2.2.le (originalMotherBudget_nonneg hN q)
  have he : (q:ℝ)*((q:ℝ)^(-(1:ℝ)/3))^2 = (q:ℝ)^(1/3:ℝ) := by
    rw [← Real.rpow_mul_natCast hq0.le]
    nth_rw 1 [← Real.rpow_one (q:ℝ)]
    rw [← Real.rpow_add hq0]
    norm_num
  apply (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hh (root_times_originalMother hN hq) 2) hq0.le).trans_eq
  simp only [mul_pow]
  rw [show (q:ℝ)*(0.6^2*((q:ℝ)^(-(1:ℝ)/3))^2*
      (8.2e-10+0.063*q/sourceL N^3)^2) =
      0.36*((q:ℝ)*((q:ℝ)^(-(1:ℝ)/3))^2)*
        (8.2e-10+(0.063/sourceL N^3)*q)^2 by ring,
    he, mul_assoc, power_affine_square hq0]
  norm_num only [show (1/3:ℝ)+1=4/3 by norm_num, show (1/3:ℝ)+2=7/3 by norm_num]
  unfold secondPolynomial
  ring

def polynomialCost (N q r : ℕ) (beta : ℝ) : MixedKind → ℝ
  | .oneEach => 3.6*Real.sqrt r*baseWeight N beta*(N:ℝ)^2*
      (firstPolynomial N q/(q.totient:ℝ)^2)
  | .oneExceptionalTwoRegular => 1.08*Real.sqrt r*baseWeight N beta*(N:ℝ)^2*
      (secondPolynomial N q/(q.totient:ℝ)^2)
  | .twoExceptionalOneRegular => 1.8*r*baseWeight N beta^2*(N:ℝ)^2*
      (firstPolynomial N q/(q.totient:ℝ)^2)

theorem normalizedCost_le_polynomial {N q r : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hq : 0 < q) (beta : ℝ) (j : MixedKind) :
    normalizedCost N q r beta (originalMotherBudget N q) j ≤ polynomialCost N q r beta j := by
  obtain ⟨hj, he, hd⟩ := roots_pos hN hq
  have hE : 0 ≤ exceptionalScale N beta := by
    unfold exceptionalScale
    exact mul_nonneg he.le (by unfold baseWeight; positivity)
  have hm : 0 ≤ originalMotherBudget N q := originalMotherBudget_nonneg hN q
  have hb : 0 ≤ baseWeight N beta := by unfold baseWeight; positivity
  have hmu : moebiusWeight q ≤ 1 := (muFactor_bounds q .linear).2
  have hJ := principalRoot_le_one
  have hB := exceptionalScale_le_base hN beta
  have hF := firstPolynomial_scale hN hq
  have hS := secondPolynomial_scale hN hq
  cases j with
  | oneEach =>
    calc
      _ = 6*moebiusWeight q*Real.sqrt r/(q.totient:ℝ)^2*(N:ℝ)^2*
          principalRoot*exceptionalScale N beta*
          (Real.sqrt q*(radiusRoot N q*originalMotherBudget N q)) := by
        unfold normalizedCost
        ring
      _ ≤ 6*1*Real.sqrt r/(q.totient:ℝ)^2*(N:ℝ)^2*1*baseWeight N beta*
          (0.6*firstPolynomial N q) := by gcongr
      _ = _ := by unfold polynomialCost; ring
  | oneExceptionalTwoRegular =>
    calc
      _ = 3*Real.sqrt r/(q.totient:ℝ)^2*(N:ℝ)^2*exceptionalScale N beta*
          ((q:ℝ)*(radiusRoot N q*originalMotherBudget N q)^2) := by
        unfold normalizedCost
        ring
      _ ≤ 3*Real.sqrt r/(q.totient:ℝ)^2*(N:ℝ)^2*baseWeight N beta*
          (0.36*secondPolynomial N q) := by gcongr
      _ = _ := by unfold polynomialCost; ring
  | twoExceptionalOneRegular =>
    calc
      _ = 3*r/(q.totient:ℝ)^2*(N:ℝ)^2*exceptionalScale N beta^2*
          (Real.sqrt q*(radiusRoot N q*originalMotherBudget N q)) := by
        unfold normalizedCost
        ring
      _ ≤ 3*r/(q.totient:ℝ)^2*(N:ℝ)^2*baseWeight N beta^2*
          (0.6*firstPolynomial N q) := by gcongr
      _ = _ := by unfold polynomialCost; ring

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
