import LiuWang.Proof.Campaign20260915.MajorArc.PaperAssembly
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.Consumer
import LiuWang.Proof.SourceRoute.LowSum.Continuation.InducedException

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException
open LiuWang.Proof.SourceRoute.MajorException.Continuation
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.MajorArc

theorem paper_source_gap {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ)) :
    Real.pi / (0.4923 * Real.sqrt d.modulus * (Real.log d.modulus) ^ 2) ≤ 1 - e.re := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have he : (e.re : ℂ) = e := by
    apply Complex.ext <;> simp [hd.2.2.1]
  have hz : d.character.LFunction (e.re : ℂ) = 0 := by
    rw [he]
    exact hd.2.1
  exact ExceptionalZeroGap.real_primitive_local_zero_gap d.isPrimitive
    (by exact_mod_cast h987) (quadratic_values_real d.character d.square_eq_one)
    (sourceP_ge_ten (exp_2000_le_of_exp_3100_le hN)) hd.1
    (by simpa only [ExceptionalZeroGap.nearOneLower, ExceptionalZeroGap.c1]
      using hd.2.2.2.2.le) hz

theorem paper_source_domain {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ)) :
    paperDomain d.modulus (sourceL N) :=
  ⟨h987, sourceL_ge_3100 hN, hd.1⟩

def paperPureIntegral (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : PureKind → ℂ
  | .linear => I15 N d e
  | .quadratic => I18 N d e
  | .cubic => I110 N d e

def rootMomentFactor (N : ℕ) (beta : ℝ) : PureKind → ℝ
  | .linear => 3 * principalRoot ^ 2 * exceptionalScale N beta * (N : ℝ) ^ 2
  | .quadratic => 3 * principalRoot * exceptionalScale N beta ^ 2 * (N : ℝ) ^ 2
  | .cubic => exceptionalScale N beta ^ 3 * (N : ℝ) ^ 2

theorem pure_root_constants :
    3 * principalRoot ^ 2 * exceptionalRoot ≤ 2.8959 ∧
      3 * principalRoot * exceptionalRoot ^ 2 ≤ 3 * quadraticHolderConstant ∧
      exceptionalRoot ^ 3 = 3 * 1.0302 * 1.0033 ^ 2 / Real.pi := by
  have hp0 : 0 ≤ principalRoot := (cubeRoot_pos (by positivity)).le
  have he0 : 0 ≤ exceptionalRoot := (cubeRoot_pos (by positivity)).le
  have hp : principalRoot ^ 3 = 2.994006 / Real.pi := cubeRoot_cube (by positivity)
  have he : exceptionalRoot ^ 3 = 3 * 1.0302 * 1.0033 ^ 2 / Real.pi :=
    cubeRoot_cube (by positivity)
  refine ⟨?_, ?_, he⟩
  · have h := scaled_young_cubic hp0 he0 (by norm_num : (0 : ℝ) < 1.013)
    rw [hp, he] at h
    have hn :
        (2 * 1.013 * (2.994006 / Real.pi) +
          (3 * 1.0302 * 1.0033 ^ 2 / Real.pi) / 1.013 ^ 2) / 3 ≤ 0.9653 := by
      convert! source_linear_holder_constant using 1
      ring
    linarith
  · have h := scaled_young_cubic he0 hp0 (by norm_num : (0 : ℝ) < 1 / 1.013)
    rw [he, hp] at h
    have hn :
        (2 * (1 / 1.013) * (3 * 1.0302 * 1.0033 ^ 2 / Real.pi) +
          (2.994006 / Real.pi) / (1 / 1.013) ^ 2) / 3 = quadraticHolderConstant := by
      unfold quadraticHolderConstant
      ring
    rw [hn] at h
    nlinarith only [h]

theorem rootMomentFactor_le_source (N : ℕ) (beta : ℝ) (j : PureKind) :
    rootMomentFactor N beta j ≤ sourceMomentFactor N beta j := by
  have hb : 0 ≤ baseWeight N beta := by unfold baseWeight; positivity
  cases j with
  | linear =>
    have h := mul_le_mul_of_nonneg_right pure_root_constants.1
      (mul_nonneg hb (sq_nonneg (N : ℝ)))
    convert! h using 1 <;> simp only [rootMomentFactor, sourceMomentFactor, exceptionalScale] <;> ring
  | quadratic =>
    have h := mul_le_mul_of_nonneg_right pure_root_constants.2.1
      (mul_nonneg (sq_nonneg (baseWeight N beta)) (sq_nonneg (N : ℝ)))
    convert! h using 1 <;> simp only [rootMomentFactor, sourceMomentFactor, exceptionalScale] <;> ring
  | cubic =>
    simp only [rootMomentFactor, sourceMomentFactor, exceptionalScale, mul_pow,
      pure_root_constants.2.2]
    exact le_of_eq (by ring)

theorem paper_pure_sum {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) (j : PureKind) :
    ‖paperPureIntegral N d e j‖ ≤ rootMomentFactor N e.re j *
      ∑ q ∈ denominators (sourceP N),
        if d.modulus ∣ q then sourceArithmeticFactor q d.modulus j else 0 := by
  have normalize (j : PureKind) :
      rootMomentFactor N e.re j *
        (∑ q ∈ denominators (sourceP N),
          if d.modulus ∣ q then sourceArithmeticFactor q d.modulus j else 0) =
      ∑ q ∈ denominators (sourceP N),
        if d.modulus ∣ q then
          rootMomentFactor N e.re j * sourceArithmeticFactor q d.modulus j else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  rw [normalize]
  cases j with
  | linear =>
    apply (I15_original_sum hN hd).trans_eq
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp only [rootMomentFactor, sourceArithmeticFactor]
    ring
  | quadratic =>
    apply (I18_original_sum hN hd).trans_eq
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp only [rootMomentFactor, sourceArithmeticFactor]
    ring
  | cubic =>
    apply (I110_original_sum hN hd).trans_eq
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp only [rootMomentFactor, sourceArithmeticFactor]
    ring

theorem paper_pure_integrals_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ))
    (hphi : (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (j : PureKind) :
    ‖paperPureIntegral N d e j‖ ≤ pureCostBudget j * (N : ℝ) ^ 2 := by
  have hmass := sourceArithmetic_paid ⌊sourceP N⌋₊ d.modulus_pos j
  have hnon :
      0 ≤ ∑ q ∈ denominators (sourceP N),
        if d.modulus ∣ q then sourceArithmeticFactor q d.modulus j else 0 :=
    Finset.sum_nonneg (fun q _ => by split_ifs; exact sourceArithmeticFactor_nonneg _ _ _; rfl)
  exact (paper_pure_sum hN hd j).trans
    ((mul_le_mul_of_nonneg_right (rootMomentFactor_le_source N e.re j) hnon).trans
      ((mul_le_mul_of_nonneg_left hmass (sourceMomentFactor_nonneg N e.re j)).trans
        (paid_cost_numeric j hN (paper_source_domain hN hd h987) hphi
          (paper_source_gap hN hd h987))))

def paperMixedIntegral (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : MixedKind → ℂ
  | .oneEach => I16 N d e
  | .oneExceptionalTwoRegular => I17 N d e
  | .twoExceptionalOneRegular => I19 N d e

theorem paper_mixed_integrals_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ))
    (hphi : (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4)
    (j : MixedKind) :
    ‖paperMixedIntegral N d e j‖ ≤ mixedBudget j * (N : ℝ) ^ 2 := by
  have hlow := fun (q : ℕ) [NeZero q] (hq : (q : ℝ) ≤ sourceP N)
      (hdq : d.modulus ∣ q) =>
    SourceRoute.LowSum.Continuation.induced_retained_weighted_bound hN hq hd hdq
  have hsum : ‖paperMixedIntegral N d e j‖ ≤ normalizedTotal N d.modulus e.re j := by
    cases j with
    | oneEach =>
      simpa only [paperMixedIntegral, normalizedTotal, normalizedCost,
        lemma2Budget, originalMotherBudget] using I16_original_sum hN hd hlow hhigh
    | oneExceptionalTwoRegular =>
      simpa only [paperMixedIntegral, normalizedTotal, normalizedCost,
        lemma2Budget, originalMotherBudget] using I17_original_sum hN hd hlow hhigh
    | twoExceptionalOneRegular =>
      simpa only [paperMixedIntegral, normalizedTotal, normalizedCost,
        lemma2Budget, originalMotherBudget] using I19_original_sum hN hd hlow hhigh
  exact (hsum.trans
    (normalizedTotal_le_analytic (exp_2000_le_of_exp_3100_le hN) d.modulus_pos e.re j)).trans
      (analyticCost_numeric hN (paper_source_domain hN hd h987) hphi
        (paper_source_gap hN hd h987) hd.2.2.2.1.le j)

theorem paper_major_lower_with_ordinary {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ))
    (hphi : (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    0.56106954 * (N : ℝ) ^ 2 + (paperOrdinaryIntegral N d e).re -
      6760 * (N : ℝ) ^ 2 / sourceL N ^ 4 ≤ (majorIntegral N).re := by
  have hp := paper_pure_integrals_paid hN hd h987 hphi
  have hm := paper_mixed_integrals_paid hN hd h987 hphi hhigh
  have h15 := (Complex.re_le_norm (-I15 N d e)).trans (by
    simpa only [norm_neg, paperPureIntegral, pureCostBudget] using hp .linear)
  have h18 := (Complex.re_le_norm (-I18 N d e)).trans (by
    simpa only [norm_neg, paperPureIntegral, pureCostBudget] using hp .quadratic)
  have h110 := (Complex.re_le_norm (-I110 N d e)).trans (by
    simpa only [norm_neg, paperPureIntegral, pureCostBudget] using hp .cubic)
  have h16 := (Complex.re_le_norm (-I16 N d e)).trans (by
    simpa only [norm_neg, paperMixedIntegral, mixedBudget] using hm .oneEach)
  have h17 := (Complex.re_le_norm (-I17 N d e)).trans (by
    simpa only [norm_neg, paperMixedIntegral, mixedBudget] using hm .oneExceptionalTwoRegular)
  have h19 := (Complex.re_le_norm (-I19 N d e)).trans (by
    simpa only [norm_neg, paperMixedIntegral, mixedBudget] using hm .twoExceptionalOneRegular)
  simp only [Complex.neg_re] at h15 h16 h17 h18 h19 h110
  linarith [majorIntegral_paper_source_lower hN hodd hd]

theorem paper_caseII_of_original_ordinary {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ))
    (hphi : (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4)
    (hordinary : -(0.00000009 * (N : ℝ) ^ 2) ≤ (paperOrdinaryIntegral N d e).re) :
    0.5577 * (N : ℝ) ^ 2 ≤ (majorIntegral N).re := by
  have hm := paper_major_lower_with_ordinary hN hodd hd h987 hphi hhigh
  have he := source_expansion_error_payment hN
  nlinarith [sq_nonneg (N : ℝ)]

#print axioms paper_pure_integrals_paid
#print axioms paper_mixed_integrals_paid
#print axioms paper_caseII_of_original_ordinary

end LiuWang.Proof.Campaign20260915.MajorArc
