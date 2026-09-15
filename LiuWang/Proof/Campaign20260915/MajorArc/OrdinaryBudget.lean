import LiuWang.Proof.Campaign20260915.MajorArc.NoninducingBudget
import LiuWang.Proof.Campaign20260915.MajorArc.PaperPayment
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.HigherConsumers

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.SingularIntegral
open LiuWang.Proof.SingularSeries.Uniform
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.SourceRoute.MajorException.Continuation
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart

namespace LiuWang.Proof.Campaign20260915.MajorArc

def ordinaryBudgetPolynomial (N q : ℕ) : ℝ :=
  0.000005 + 0.063 * (q : ℝ) / sourceP N

theorem ordinaryBudgetPolynomial_bounds {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    0 < ordinaryBudgetPolynomial N q ∧ ordinaryBudgetPolynomial N q ≤ 0.064 := by
  have hp := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  have hfrac := (div_le_one hp).mpr hq
  unfold ordinaryBudgetPolynomial
  constructor
  · positivity
  · rw [mul_div_assoc]
    linarith

theorem ordinaryMass_all_moduli {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hhigh : WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    ordinaryMass N q d e ≤ ordinaryBudgetPolynomial N q / sourceL N := by
  have hh :
      (∑ chi : Character q,
        ∑ rho ∈ (retainedValues chi (sourceT N) d e).filter
          (fun rho => omegaCutoff N q < |rho.im|),
            (zeroMultiplicity chi rho : ℝ) * highWeight N rho) ≤
        WeightedHighZeros.highSum N q := by
    change _ ≤ ∑ chi : Character q, ∑ rho ∈ WeightedHighZeros.highValues N chi,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * ((N : ℝ) ^ (rho.re - 1) / |rho.im|)
    apply Finset.sum_le_sum
    intro chi _
    simp only [zeroMultiplicity, highWeight, baseWeight]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro rho hr
      obtain ⟨hr, ht⟩ := Finset.mem_filter.mp hr
      rw [WeightedHighZeros.highValues_eq_complete]
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, ht.le⟩
    · intro rho _ _
      positivity
  rw [ordinaryMass_split hN]
  apply (add_le_add (retained_low_all_moduli hN hq hd)
    (mul_le_mul_of_nonneg_left (hh.trans hhigh) (by norm_num : (0 : ℝ) ≤ 5))).trans_eq
  unfold ordinaryBudgetPolynomial sourceP
  ring

theorem ordinary_kernel_moment_bound {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : Nat.Coprime a q)
    (d : PrimitiveQuadraticDatum) (e : ℂ) {M : ℝ} (hM : 0 < M)
    (hm : ordinaryMass N q d e ≤ M) :
    ‖∫ eta in -deltaRadius N q..deltaRadius N q,
      paperOrdinaryKernel N a q d e eta * arcPhase N a q eta‖ ≤
        (N : ℝ) ^ 2 *
          (3 * (1 / (q.totient : ℝ)) ^ 2 *
              (Real.sqrt q / q.totient * radiusRoot N q * M) +
            3 * (1 / (q.totient : ℝ)) *
              (Real.sqrt q / q.totient * radiusRoot N q * M) ^ 2 +
            (Real.sqrt q / q.totient * radiusRoot N q * M) ^ 3) := by
  have hn := nat_pos_of_exp_le hN
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hdelta := (deltaRadius_pos hN' (NeZero.pos q)).le
  have hphi : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  let A : ℝ := 1 / q.totient
  let B : ℝ := Real.sqrt q / q.totient * radiusRoot N q * M
  let f : ℝ → ℂ := fun eta => principalCoefficient q * J N eta
  let g : ℝ → ℂ := ordinaryPacket N a q d e
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by
    have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos q))
    have hr := (roots_pos hN' (NeZero.pos q)).2.2
    dsimp [B]
    positivity
  have hf : Continuous f := continuous_const.mul (continuous_J hn)
  have hg : Continuous g := ordinaryPacket_continuous hn a d e
  have hp := continuous_arcPhase N a q
  have hc : ‖principalCoefficient q‖ ≤ A := by
    rw [norm_principalCoefficient]
    have hmu : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> rw [h] <;> norm_num
    exact div_le_div_of_nonneg_right hmu hphi.le
  have hj : (∫ eta in -deltaRadius N q..deltaRadius N q, ‖J N eta‖ ^ 3) ≤
      (N : ℝ) ^ 2 := by
    have h := principal_cubic_bound hn hdelta
    simp only [Jrho_one_eq_J] at h
    exact h.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (roots_pos hN' (NeZero.pos q)).1.le principalRoot_le_one 3)
      (sq_nonneg (N : ℝ))).trans_eq (by ring))
  have hfm : (∫ eta in -deltaRadius N q..deltaRadius N q, ‖f eta‖ ^ 3) ≤
      (N : ℝ) ^ 2 * A ^ 3 := by
    simp only [f, norm_mul, mul_pow, intervalIntegral.integral_const_mul]
    exact ((mul_le_mul_of_nonneg_left hj (pow_nonneg (norm_nonneg _) 3)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hc 3)
        (sq_nonneg (N : ℝ)))).trans_eq (mul_comm _ _)
  have hgm : (∫ eta in -deltaRadius N q..deltaRadius N q, ‖g eta‖ ^ 3) ≤
      (N : ℝ) ^ 2 * B ^ 3 := ordinaryPacket_cubic hN ha d e hm
  have h1 := continuous_triple_holder f f g (arcPhase N a q) hf hf hg hp
    (norm_arcPhase N a q) hdelta hA hA hB hfm hfm hgm
  have h2 := continuous_triple_holder f g g (arcPhase N a q) hf hg hg hp
    (norm_arcPhase N a q) hdelta hA hB hB hfm hgm hgm
  have h3 := continuous_triple_holder g g g (arcPhase N a q) hg hg hg hp
    (norm_arcPhase N a q) hdelta hB hB hB hgm hgm hgm
  have he :
      (∫ eta in -deltaRadius N q..deltaRadius N q,
        paperOrdinaryKernel N a q d e eta * arcPhase N a q eta) =
      (-3 : ℂ) * (∫ eta in -deltaRadius N q..deltaRadius N q,
        f eta * f eta * g eta * arcPhase N a q eta) +
      (3 : ℂ) * (∫ eta in -deltaRadius N q..deltaRadius N q,
        f eta * g eta * g eta * arcPhase N a q eta) -
      (∫ eta in -deltaRadius N q..deltaRadius N q,
        g eta * g eta * g eta * arcPhase N a q eta) := by
    have hi1 : IntervalIntegrable (fun eta =>
        (-3 : ℂ) * (f eta * f eta * g eta * arcPhase N a q eta))
        volume (-deltaRadius N q) (deltaRadius N q) :=
      (continuous_const.mul (((hf.mul hf).mul hg).mul hp)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun eta =>
        (3 : ℂ) * (f eta * g eta * g eta * arcPhase N a q eta))
        volume (-deltaRadius N q) (deltaRadius N q) :=
      (continuous_const.mul (((hf.mul hg).mul hg).mul hp)).intervalIntegrable _ _
    have hi3 : IntervalIntegrable (fun eta => g eta * g eta * g eta * arcPhase N a q eta)
        volume (-deltaRadius N q) (deltaRadius N q) :=
      (((hg.mul hg).mul hg).mul hp).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hi1 hi2, ← intervalIntegral.integral_sub (hi1.add hi2) hi3]
    congr 1
    ext eta
    simp only [paperOrdinaryKernel, dif_neg (NeZero.ne q), f, g]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_mul, norm_neg, Complex.norm_ofNat]
  have h := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3))
      (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 3))) h3
  convert! h using 1
  dsimp [A, B]
  ring

theorem ordinary_scale_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    Real.sqrt q / q.totient * radiusRoot N q *
        (ordinaryBudgetPolynomial N q / sourceL N) ≤
      0.6 * ((q : ℝ) ^ (1 / 6 : ℝ) / q.totient) * ordinaryBudgetPolynomial N q := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN'
  have hm : 0 ≤ ordinaryBudgetPolynomial N q := by
    unfold ordinaryBudgetPolynomial
    have hp := sourceP_pos hN'
    positivity
  have hs : Real.sqrt q * (q : ℝ) ^ (-(1 : ℝ) / 3) = (q : ℝ) ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (Nat.cast_pos.mpr (NeZero.pos q))]
    norm_num
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (radiusRoot_le_power hN' (NeZero.pos q)) (by positivity))
    (div_nonneg hm hL.le)).trans_eq
  calc
    _ = 0.6 * (Real.sqrt q * (q : ℝ) ^ (-(1 : ℝ) / 3) / q.totient) *
        ordinaryBudgetPolynomial N q := by field_simp
    _ = _ := by rw [hs]

theorem ordinary_polynomial_coarse {t m : ℝ} (ht : 1 ≤ t) (hm : 0 ≤ m) (hm1 : m ≤ 0.064) :
    1.8 * t * m + 1.08 * t ^ 2 * m ^ 2 + 0.216 * t ^ 3 * m ^ 3 ≤ 1.9 * t ^ 3 * m := by
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ t ^ 3 := by nlinarith [sq_nonneg (t - 1)]
  have ht2 : t ^ 2 ≤ t ^ 3 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht)]
  have h : 1.8 * t + 1.08 * t ^ 2 * m + 0.216 * t ^ 3 * m ^ 2 ≤ 1.9 * t ^ 3 := by
    calc
      _ ≤ 1.8 * t ^ 3 + 1.08 * t ^ 3 * 0.064 + 0.216 * t ^ 3 * 0.064 ^ 2 := by gcongr
      _ ≤ _ := by nlinarith [pow_nonneg ht0 3]
  convert! mul_le_mul_of_nonneg_right h hm using 1
  ring

theorem ordinary_arc_all_moduli {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hhigh : WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    ‖∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
      paperOrdinaryKernel N a q d e eta * arcPhase N a q eta‖ ≤
        1.9 * (N : ℝ) ^ 2 * (Real.sqrt q / (q.totient : ℝ) ^ 2) *
          ordinaryBudgetPolynomial N q := by
  have hphi : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hm := ordinaryBudgetPolynomial_bounds hN hq
  let t := (q : ℝ) ^ (1 / 6 : ℝ)
  have ht : 1 ≤ t := Real.one_le_rpow (by exact_mod_cast NeZero.pos q) (by norm_num)
  have ht3 : t ^ 3 = Real.sqrt q := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q), Real.sqrt_eq_rpow]
    norm_num
  have hs := ordinary_scale_bound (q := q) hN
  have hs0 : 0 ≤ Real.sqrt q / q.totient * radiusRoot N q *
      (ordinaryBudgetPolynomial N q / sourceL N) := by
    have hr := (roots_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)).2.2
    have hm0 := hm.1.le
    positivity
  have hbound : ‖∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
      paperOrdinaryKernel N a q d e eta * arcPhase N a q eta‖ ≤
      (q.totient : ℝ) * ((N : ℝ) ^ 2 *
        (3 * (1 / (q.totient : ℝ)) ^ 2 * (0.6 * (t / q.totient) * ordinaryBudgetPolynomial N q) +
          3 * (1 / (q.totient : ℝ)) * (0.6 * (t / q.totient) * ordinaryBudgetPolynomial N q) ^ 2 +
          (0.6 * (t / q.totient) * ordinaryBudgetPolynomial N q) ^ 3)) := by
    apply SourceRoute.MajorOrdinary.norm_sum_numerators_le
    intro a ha
    apply (ordinary_kernel_moment_bound hN (mem_numerators.mp ha).2.2 d e
      (div_pos hm.1 hL) (ordinaryMass_all_moduli hN hq hd hhigh)).trans
    gcongr
  apply hbound.trans
  calc
    _ = ((N : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        (1.8 * t * ordinaryBudgetPolynomial N q +
          1.08 * t ^ 2 * ordinaryBudgetPolynomial N q ^ 2 +
          0.216 * t ^ 3 * ordinaryBudgetPolynomial N q ^ 3) := by field_simp; ring
    _ ≤ ((N : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        (1.9 * t ^ 3 * ordinaryBudgetPolynomial N q) :=
      mul_le_mul_of_nonneg_left (ordinary_polynomial_coarse ht hm.1.le hm.2) (by positivity)
    _ = _ := by rw [ht3]; ring

theorem ordinary_budget_sum {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∑ q ∈ denominators (sourceP N), (Real.sqrt q / (q.totient : ℝ) ^ 2) *
      ordinaryBudgetPolynomial N q) ≤ 0.000076 := by
  have hP := SourceRoute.MajorOrdinary.Continuation.sourceP_ge_ten_billion hN
  have hl := unweighted_half_moment (P := sourceP N) (by linarith)
  have hh := unweighted_three_halves_normalized hP
  have he :
      (∑ q ∈ denominators (sourceP N), (Real.sqrt q / (q.totient : ℝ) ^ 2) *
        ordinaryBudgetPolynomial N q) =
      0.000005 * squareSum (SourceRoute.MajorOrdinary.Continuation.totientRatioPower (1 / 2))
        ⌊sourceP N⌋₊ +
        0.063 * (squareSum (SourceRoute.MajorOrdinary.Continuation.totientRatioPower (3 / 2))
          ⌊sourceP N⌋₊ / sourceP N) := by
    have hpoly (q : ℕ) : ordinaryBudgetPolynomial N q =
        0.000005 + (0.063 / sourceP N) * q := by unfold ordinaryBudgetPolynomial; ring
    simp_rw [hpoly, Real.sqrt_eq_rpow]
    rw [unweighted_linear_sum]
    norm_num only
    ring
  rw [he]
  linarith

theorem paperOrdinaryIntegral_norm_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    ‖paperOrdinaryIntegral N d e‖ ≤ 0.00015 * (N : ℝ) ^ 2 := by
  rw [paperOrdinaryIntegral, coreIndices, Finset.sum_sigma]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ denominators (sourceP N),
        1.9 * (N : ℝ) ^ 2 * (Real.sqrt q / (q.totient : ℝ) ^ 2) *
          ordinaryBudgetPolynomial N q := by
      apply Finset.sum_le_sum
      intro q hq
      have hqs := (mem_denominators (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le q).mp hq
      let : NeZero q := ⟨by omega⟩
      exact ordinary_arc_all_moduli hN hqs.2 hd (hhigh q hqs.2)
    _ = 1.9 * (N : ℝ) ^ 2 *
        ∑ q ∈ denominators (sourceP N), (Real.sqrt q / (q.totient : ℝ) ^ 2) *
          ordinaryBudgetPolynomial N q := by rw [Finset.mul_sum]; congr 1; funext q; ring
    _ ≤ 1.9 * (N : ℝ) ^ 2 * 0.000076 :=
      mul_le_mul_of_nonneg_left (ordinary_budget_sum hN) (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg (N : ℝ)]

theorem paperOrdinaryIntegral_signed_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    -(0.00015 * (N : ℝ) ^ 2) ≤ (paperOrdinaryIntegral N d e).re := by
  have hr := Complex.re_le_norm (-paperOrdinaryIntegral N d e)
  simp only [Complex.neg_re, norm_neg] at hr
  linarith [paperOrdinaryIntegral_norm_paid hN hd hhigh]

theorem paper_caseII_ordinary_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ))
    (hphi : (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    0.5577 * (N : ℝ) ^ 2 ≤ (majorIntegral N).re := by
  have hm := paper_major_lower_with_ordinary hN hodd hd h987 hphi
    (fun q _ hq _ => hhigh q hq)
  have ho := paperOrdinaryIntegral_signed_paid hN hd hhigh
  have he := source_expansion_error_payment hN
  nlinarith [sq_nonneg (N : ℝ)]

#print axioms paperOrdinaryIntegral_signed_paid
#print axioms paper_caseII_ordinary_paid

end LiuWang.Proof.Campaign20260915.MajorArc
