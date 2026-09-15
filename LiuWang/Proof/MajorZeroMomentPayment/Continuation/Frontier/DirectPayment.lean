import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.DirectMoment

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier

def regularRhoWeight {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℝ :=
  ∑ rho ∈ regularValues N chi,
    (analyticOrderNatAt chi.LFunction rho : ℝ) * (baseWeight N rho.re / ‖rho‖)

def directArithmeticSum (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : Character q, ‖linearCoefficient N chi‖ * regularRhoWeight N chi

def directLinearCost (N q : ℕ) : ℝ :=
  (16/Real.pi) * (N : ℝ)^2 * radiusLog N q * directArithmeticSum N q

theorem radiusLog_nonneg {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    0 ≤ radiusLog N q := by
  have hP := sourceP_pos hN
  apply Real.log_nonneg
  have hp : 0 ≤ 0.336 * sourceP N / (q : ℝ) := by positivity
  linarith

theorem norm_regularLinearArc_direct {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖regularLinearArc N q‖ ≤ directLinearCost N q := by
  rw [regularLinearArc_eq_moments (nat_pos_of_exp_le hN)]
  have hfac : 0 ≤ (16/Real.pi) * (N : ℝ)^2 * radiusLog N q :=
    mul_nonneg (by positivity) (radiusLog_nonneg hN)
  unfold directLinearCost directArithmeticSum
  rw [dif_neg (NeZero.ne q), Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro chi _
  rw [regularRhoWeight, Finset.mul_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro rho hr
  have hv := mem_zeroValues.mp (Finset.mem_filter.mp hr).1
  have hr0 : rho ≠ 0 := by intro he; simp [he] at hv
  have hb := actual_finiteMoment_direct hN (NeZero.pos q) hv.2.1.le hr0
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤
    ‖linearCoefficient N chi‖ * (analyticOrderNatAt chi.LFunction rho : ℝ))).trans_eq
  ring

def enhancedRegularPayment (N q : ℕ) : ℝ :=
  max (localRegularLinearPayment N q) (-directLinearCost N q)

theorem enhancedRegularPayment_lower {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    enhancedRegularPayment N q ≤ (regularLinearArc N q).re := by
  apply max_le (regularLinearArc_payment hN)
  have he := Complex.re_le_norm (-regularLinearArc N q)
  rw [Complex.neg_re, norm_neg] at he
  linarith [norm_regularLinearArc_direct (q := q) hN]

theorem directArithmeticSum_divisor {N q : ℕ} [NeZero q] (hd : q ∣ N) :
    directArithmeticSum N q =
      ‖linearCoefficient N (1 : Character q)‖ * regularRhoWeight N (1 : Character q) := by
  simp only [directArithmeticSum, dif_neg (NeZero.ne q)]
  apply Fintype.sum_eq_single (1 : Character q)
  intro chi hc
  simp [linearCoefficient_divisor_nonprincipal hd hc]

theorem regularRhoWeight_nonneg {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    0 ≤ regularRhoWeight N chi := by
  apply Finset.sum_nonneg
  intro rho _
  unfold baseWeight
  positivity

theorem gaussScale_norm_le {q : ℕ} [NeZero q] (chi : Character q) :
    ‖gaussScale chi‖ ≤ (q.totient : ℝ)⁻¹ * Real.sqrt chi⁻¹.conductor := by
  rw [gaussScale, norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_gaussSum_le_sqrt_conductor chi⁻¹) (by positivity)

theorem linearCoefficient_norm_arithmetic {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    ‖linearCoefficient N chi‖ ≤
      3 * ‖principalCoefficient q‖^2 *
        ((q.totient : ℝ)⁻¹ * Real.sqrt chi⁻¹.conductor) * arithmeticWeight N chi := by
  rw [linearCoefficient, norm_mul, norm_mul, norm_mul, norm_pow]
  norm_num only [norm_neg, Complex.norm_ofNat]
  apply mul_le_mul
    (mul_le_mul_of_nonneg_left (gaussScale_norm_le chi) (by positivity))
    (norm_phaseCoefficient_le_weight N chi) (norm_nonneg _) (by positivity)

theorem directArithmeticSum_le_conductor {q : ℕ} [NeZero q] (N : ℕ) :
    directArithmeticSum N q ≤
      ∑ chi : Character q,
        (3 * ‖principalCoefficient q‖^2 *
          ((q.totient : ℝ)⁻¹ * Real.sqrt chi⁻¹.conductor) * arithmeticWeight N chi) *
          regularRhoWeight N chi := by
  simp only [directArithmeticSum, dif_neg (NeZero.ne q)]
  exact Finset.sum_le_sum (fun chi _ =>
    mul_le_mul_of_nonneg_right (linearCoefficient_norm_arithmetic N chi)
      (regularRhoWeight_nonneg N chi))

def totalEnhancedRegularPayment (N : ℕ) : ℝ :=
  ∑ q ∈ denominators (sourceP N), enhancedRegularPayment N q

theorem enhancedPayment_preserves_signed (N : ℕ) :
    totalRegularLinearPayment N ≤ totalEnhancedRegularPayment N :=
  Finset.sum_le_sum (fun _ _ => le_max_left _ _)

theorem enhancedPayment_integral {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    totalEnhancedRegularPayment N ≤ (regularLinearIntegral N).re := by
  rw [totalEnhancedRegularPayment, regularLinearIntegral, Complex.re_sum]
  apply Finset.sum_le_sum
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact enhancedRegularPayment_lower hN

theorem actual_finite_direct_gamma {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : 0 < q) {rho : ℂ} (hb : 0 ≤ rho.re) (hg : 0 < |rho.im|) :
    ‖finiteMoment N (deltaRadius N q) 1 1 rho‖ ≤
      (16/Real.pi) * (N : ℝ)^2 * radiusLog N q * (baseWeight N rho.re / |rho.im|) := by
  have hr : rho ≠ 0 := by intro he; simp [he] at hg
  apply (actual_finiteMoment_direct hN hq hb hr).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (radiusLog_nonneg hN))
  exact div_le_div_of_nonneg_left (by unfold baseWeight; positivity) hg (Complex.abs_im_le_norm rho)

theorem regularLinearArc_weighted_budget {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {b : ℝ}
    (hb : directArithmeticSum N q ≤ b) :
    ‖regularLinearArc N q‖ ≤ 5.1 * (N : ℝ)^2 * radiusLog N q * b := by
  have hsum : 0 ≤ directArithmeticSum N q := by
    simp only [directArithmeticSum, dif_neg (NeZero.ne q)]
    exact Finset.sum_nonneg (fun chi _ => mul_nonneg (norm_nonneg _) (regularRhoWeight_nonneg N chi))
  have hc : (16 : ℝ)/Real.pi ≤ 5.1 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_d4]
  apply (norm_regularLinearArc_direct hN).trans
  unfold directLinearCost
  apply mul_le_mul _ hb hsum (by have := radiusLog_nonneg (q := q) hN; positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ))) (radiusLog_nonneg hN)

theorem lambdaTripleCount_direct_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.48166084 * (N : ℝ)^2 + totalAllModuliExceptionalPayment N +
      totalEnhancedRegularPayment N + (regularHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ lambdaTripleCount N := by
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split (exp_2000_le_of_exp_3100_le hN), Complex.add_re] at h
  linarith [exceptionalIntegral_allModuli_payment (exp_2000_le_of_exp_3100_le hN),
    enhancedPayment_integral (exp_2000_le_of_exp_3100_le hN)]

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier
