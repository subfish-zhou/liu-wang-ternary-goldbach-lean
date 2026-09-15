import LiuWang.Proof.MajorZeroInteraction.Signed
import LiuWang.Proof.ZeroRegionFamily.RealClosure.Consumer

/-! The exceptional split uses the proved R24 region, not the unproved
source constant 9.645908801. One actual family witness controls every modulus. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.MajorZeroInteraction

def exceptionalValues {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : Finset ℂ :=
  (zeroValues chi (sourceT N)).filter (RealClosure.region (sourceP N) q)

def exceptionalCoefficient {q : ℕ} [NeZero q] (N : ℕ) (eta : ℝ)
    (chi : Character q) : ℂ :=
  (q.totient : ℂ)⁻¹ * gaussSum chi⁻¹ ZMod.stdAddChar *
    ∑ rho ∈ exceptionalValues N chi,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def regularCoefficient {q : ℕ} [NeZero q] (N : ℕ) (eta : ℝ)
    (chi : Character q) : ℂ :=
  (q.totient : ℂ)⁻¹ * gaussSum chi⁻¹ ZMod.stdAddChar *
    ∑ rho ∈ (zeroValues chi (sourceT N)).filter
      (fun rho => ¬ RealClosure.region (sourceP N) q rho),
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem coefficient_regular_add_exceptional {q : ℕ} [NeZero q]
    (N : ℕ) (eta : ℝ) (chi : Character q) :
    zeroCoefficient N eta chi =
      regularCoefficient N eta chi + exceptionalCoefficient N eta chi := by
  unfold zeroCoefficient zeroValueSum regularCoefficient exceptionalCoefficient exceptionalValues
  rw [← mul_add, add_comm, Finset.sum_filter_add_sum_filter_not]

theorem sourceP_ge_ten {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    10 ≤ sourceP N := by
  have h := sourceL_ge_2000 hN
  unfold sourceP
  nlinarith [sq_nonneg (sourceL N), mul_nonneg (by linarith : 0 ≤ sourceL N - 2000)
    (sq_nonneg (sourceL N))]

theorem exceptionalValues_quadratic_simple {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    chi ≠ 1 ∧ chi^2 = 1 ∧ rho.im = 0 ∧ analyticOrderNatAt chi.LFunction rho = 1 := by
  obtain ⟨hz, hreg⟩ := Finset.mem_filter.mp hr
  have hv := mem_zeroValues.mp hz
  have hp : rho ≠ 1 := by
    intro he
    exact zeroValues_pole_excluded chi (sourceT N) (he ▸ hz)
  exact RealClosure.zero_real_quadratic_simple (sourceP_ge_ten hN) hq chi
    hreg (Or.inr hp) hv.1

theorem exceptionalValues_same_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ sourceP N ∧
      d.modulus = chi.conductor ∧ inducedAt d q = chi ∧ datumL d rho = 0 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ sourceP N →
        ∀ (psi : Character r) (tau : ℂ), tau ∈ exceptionalValues N psi →
          tau = rho ∧ d.modulus = psi.conductor ∧ d.modulus ∣ r ∧
            inducedAt d r = psi ∧ analyticOrderNatAt psi.LFunction tau = 1 := by
  obtain ⟨hz, hreg⟩ := Finset.mem_filter.mp hr
  have hp : rho ≠ 1 := by
    intro he
    exact zeroValues_pole_excluded chi (sourceT N) (he ▸ hz)
  obtain ⟨d, hd, hdc, hdi, hdz, _, _, hall⟩ :=
    RealClosure.family_fixed_source (sourceP_ge_ten hN) hq chi hreg (Or.inr hp)
      (mem_zeroValues.mp hz).1
  refine ⟨d, hd, hdc, hdi, hdz, ?_⟩
  intro r _ hrq psi tau ht
  obtain ⟨htz, htr⟩ := Finset.mem_filter.mp ht
  have htp : tau ≠ 1 := by
    intro he
    exact zeroValues_pole_excluded psi (sourceT N) (he ▸ htz)
  exact hall r hrq psi tau htr (Or.inr htp) (mem_zeroValues.mp htz).1

theorem exceptionalValues_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    exceptionalValues N chi = {rho} := by
  ext tau
  constructor
  · intro ht
    obtain ⟨d, _, _, _, _, hall⟩ := exceptionalValues_same_source hN hq hr
    exact Finset.mem_singleton.mpr (hall q hq chi tau ht).1
  · intro ht
    simpa only [Finset.mem_singleton.mp ht] using hr

theorem exceptionalValues_other_character {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    {psi : Character q} (hne : psi ≠ chi) :
    exceptionalValues N psi = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro tau ht
  obtain ⟨d, _, _, hdi, _, hall⟩ := exceptionalValues_same_source hN hq hr
  exact hne ((hall q hq psi tau ht).2.2.2.1.symm.trans hdi)

theorem exceptionalCoefficient_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (eta : ℝ) :
    exceptionalCoefficient N eta chi =
      (q.totient : ℂ)⁻¹ * gaussSum chi⁻¹ ZMod.stdAddChar * Jrho N rho eta := by
  rw [exceptionalCoefficient, exceptionalValues_at_witness hN hq hr]
  simp only [Finset.sum_singleton, (exceptionalValues_quadratic_simple hN hq hr).2.2.2,
    Nat.cast_one, one_mul]

theorem exceptional_evaluation_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (a : ℕ) (eta : ℝ) :
    characterEvaluation (exceptionalCoefficient (q := q) N eta) a =
      chi (a : ZMod q) * exceptionalCoefficient N eta chi := by
  unfold characterEvaluation
  apply Fintype.sum_eq_single chi
  intro psi hne
  rw [exceptionalCoefficient, exceptionalValues_other_character hN hq hr hne,
    Finset.sum_empty, mul_zero, mul_zero]

theorem no_exceptional_coefficient {N q : ℕ} [NeZero q]
    (hnone : ∀ chi : Character q, exceptionalValues N chi = ∅)
    (eta : ℝ) (chi : Character q) :
    exceptionalCoefficient N eta chi = 0 ∧
      zeroCoefficient N eta chi = regularCoefficient N eta chi := by
  have hz : exceptionalCoefficient N eta chi = 0 := by
    simp only [exceptionalCoefficient, hnone chi, Finset.sum_empty, mul_zero]
  exact ⟨hz, by rw [coefficient_regular_add_exceptional, hz, add_zero]⟩

def exceptionalKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let E := characterEvaluation (exceptionalCoefficient (q := q) N eta) a;
    -3 * (principalCoefficient q * J N eta)^2 * E +
      3 * (principalCoefficient q * J N eta) * E^2 - E^3

theorem exceptional_numerator_contraction {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (eta : ℝ) :
    (∑ a ∈ numerators q, exceptionalKernel N a q eta *
      charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))) =
      (-3 * (principalCoefficient q * J N eta)^2 * exceptionalCoefficient N eta chi -
        exceptionalCoefficient N eta chi^3) * phaseCoefficient N chi +
      3 * (principalCoefficient q * J N eta) * exceptionalCoefficient N eta chi^2 *
        ramanujan N q := by
  have hs := (exceptionalValues_quadratic_simple hN hq hr).2.1
  have he (a : ℕ) (ha : a ∈ numerators q) :
      exceptionalKernel N a q eta =
        (-3 * (principalCoefficient q * J N eta)^2 * exceptionalCoefficient N eta chi -
          exceptionalCoefficient N eta chi^3) * chi (a : ZMod q) +
        3 * (principalCoefficient q * J N eta) * exceptionalCoefficient N eta chi^2 := by
    have hsq : chi (a : ZMod q)^2 = 1 := by
      have hx := congrArg (fun psi : Character q => psi (a : ZMod q)) hs
      have hu := (ZMod.isUnit_iff_coprime a q).mpr (mem_numerators.mp ha).2.2
      simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using hx
    have hcube : chi (a : ZMod q)^3 = chi (a : ZMod q) := by
      rw [pow_succ, hsq, one_mul]
    simp only [exceptionalKernel, dif_neg (NeZero.ne q),
      exceptional_evaluation_at_witness hN hq hr, mul_pow, hsq, hcube]
    ring
  rw [phaseCoefficient, ramanujan, Finset.mul_sum, Finset.mul_sum]
  simp only [numerators, SingularSeries.reducedResidues]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [he a ha]
  ring

theorem exceptional_divisor_contraction {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hd : q ∣ N) (eta : ℝ) :
    (∑ a ∈ numerators q, exceptionalKernel N a q eta *
      charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))) =
      3 * (principalCoefficient q * J N eta) * exceptionalCoefficient N eta chi^2 *
        ramanujan N q := by
  rw [exceptional_numerator_contraction hN hq hr,
    phaseCoefficient_vanishes hd (exceptionalValues_quadratic_simple hN hq hr).1,
    mul_zero, zero_add]

def regularInteractionKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let E := characterEvaluation (exceptionalCoefficient (q := q) N eta) a
    let R := characterEvaluation (regularCoefficient (q := q) N eta) a;
    -3 * (principalCoefficient q * J N eta - E)^2 * R +
      3 * (principalCoefficient q * J N eta - E) * R^2 - R^3

theorem interaction_exceptional_add_regular {q : ℕ} [NeZero q]
    (N a : ℕ) (eta : ℝ) (ha : Nat.Coprime a q) :
    interactionKernel N a q eta =
      exceptionalKernel N a q eta + regularInteractionKernel N a q eta := by
  have hz : characterEvaluation (zeroCoefficient (q := q) N eta) a =
      characterEvaluation (regularCoefficient (q := q) N eta) a +
        characterEvaluation (exceptionalCoefficient (q := q) N eta) a := by
    simp only [characterEvaluation, coefficient_regular_add_exceptional,
      mul_add, Finset.sum_add_distrib]
  rw [interactionKernel, packet_eq_evaluation N a eta ha, hz]
  simp only [exceptionalKernel, regularInteractionKernel, dif_neg (NeZero.ne q)]
  ring

theorem interaction_no_exceptional {q : ℕ} [NeZero q]
    (N a : ℕ) (eta : ℝ) (ha : Nat.Coprime a q)
    (hnone : ∀ chi : Character q, exceptionalValues N chi = ∅) :
    exceptionalKernel N a q eta = 0 ∧
      interactionKernel N a q eta = regularInteractionKernel N a q eta := by
  have he : exceptionalKernel N a q eta = 0 := by
    simp only [exceptionalKernel, dif_neg (NeZero.ne q), characterEvaluation,
      (no_exceptional_coefficient hnone eta _).1, mul_zero, Finset.sum_const_zero,
      zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), zero_add, sub_zero]
  exact ⟨he, by rw [interaction_exceptional_add_regular N a eta ha, he, zero_add]⟩

theorem continuous_exceptionalCoefficient {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) : Continuous (fun eta => exceptionalCoefficient N eta chi) := by
  unfold exceptionalCoefficient
  exact continuous_const.mul (continuous_finsetSum _ fun rho _ =>
    continuous_const.mul (SingularIntegral.Jrho_continuous hN rho))

theorem continuous_exceptionalKernel {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (exceptionalKernel N a q) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    have he : Continuous (fun eta =>
        characterEvaluation (exceptionalCoefficient (q := q) N eta) a) :=
      continuous_finsetSum _ fun chi _ =>
        continuous_const.mul (continuous_exceptionalCoefficient hN chi)
    have hm : Continuous (fun eta => principalCoefficient q * J N eta) :=
      continuous_const.mul (continuous_J hN)
    unfold exceptionalKernel
    simp only [dif_neg hq]
    exact (((continuous_const.mul (hm.pow 2)).mul he).add
      ((continuous_const.mul hm).mul (he.pow 2))).sub (he.pow 3)

theorem exceptional_arc_contraction {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    (∑ a ∈ numerators q,
      ∫ eta in -deltaRadius N q..deltaRadius N q,
        exceptionalKernel N a q eta * arcPhase N a q eta) =
      (∫ eta in -deltaRadius N q..deltaRadius N q,
        ((-3 * (principalCoefficient q * J N eta)^2 *
            exceptionalCoefficient N eta chi - exceptionalCoefficient N eta chi^3) *
              phaseCoefficient N chi +
          3 * (principalCoefficient q * J N eta) *
            exceptionalCoefficient N eta chi^2 * ramanujan N q) *
          charReal (-(N : ℝ) * eta)) := by
  rw [← intervalIntegral.integral_finsetSum
    (f := fun a eta => exceptionalKernel N a q eta * arcPhase N a q eta) (fun a _ =>
    ((continuous_exceptionalKernel (nat_pos_of_exp_le hN) a q).mul
      (continuous_arcPhase N a q)).intervalIntegrable _ _)]
  congr 1
  ext eta
  simp only [arcPhase_split, ← mul_assoc, ← Finset.sum_mul]
  rw [exceptional_numerator_contraction hN hq hr]
  ring

theorem exceptional_arc_divisor {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hd : q ∣ N) :
    (∑ a ∈ numerators q,
      ∫ eta in -deltaRadius N q..deltaRadius N q,
        exceptionalKernel N a q eta * arcPhase N a q eta) =
      (∫ eta in -deltaRadius N q..deltaRadius N q,
        3 * (principalCoefficient q * J N eta) *
          exceptionalCoefficient N eta chi^2 * ramanujan N q *
            charReal (-(N : ℝ) * eta)) := by
  rw [exceptional_arc_contraction hN hq hr]
  simp only [phaseCoefficient_vanishes hd (exceptionalValues_quadratic_simple hN hq hr).1,
    mul_zero, zero_add]

def exceptionalIntegral (N : ℕ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    exceptionalKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta

def regularInteractionIntegral (N : ℕ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    regularInteractionKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta

theorem interactionIntegral_exceptional_add_regular {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    interactionIntegral N = exceptionalIntegral N + regularInteractionIntegral N := by
  rw [interactionIntegral, exceptionalIntegral, regularInteractionIntegral,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have ha := ((mem_coreIndices hN i).mp hi).2.2.2
  let : NeZero i.1 :=
    ⟨(ArcGeometry.sourceIndex_den_pos ((mem_coreIndices hN i).mp hi).2).ne'⟩
  have he : IntervalIntegrable (fun eta =>
      exceptionalKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta)
      volume (-deltaRadius N i.1) (deltaRadius N i.1) :=
    ((continuous_exceptionalKernel (nat_pos_of_exp_le hN) i.2 i.1).mul
      (continuous_arcPhase N i.2 i.1)).intervalIntegrable _ _
  have hr : IntervalIntegrable (fun eta =>
      regularInteractionKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta)
      volume (-deltaRadius N i.1) (deltaRadius N i.1) := by
    have hh := (interaction_integrable (nat_pos_of_exp_le hN) i.2 i.1
      (-deltaRadius N i.1) (deltaRadius N i.1)).sub he
    convert hh using 1
    ext eta
    rw [interaction_exceptional_add_regular N i.2 eta ha, add_mul]
    ring
  rw [← intervalIntegral.integral_add he hr]
  congr 1
  ext eta
  rw [interaction_exceptional_add_regular N i.2 eta ha, add_mul]

theorem lambdaTripleCount_ge_exceptional_regular {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.48166084 * (N : ℝ)^2 + (exceptionalIntegral N).re +
      (regularInteractionIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ) * alpha)).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ lambdaTripleCount N := by
  have h := CircleLowerBound.lambdaTripleCount_ge_strong hN hodd
  rw [interactionIntegral_exceptional_add_regular (exp_2000_le_of_exp_3100_le hN),
    Complex.add_re] at h
  linarith

end LiuWang.Proof.MajorZeroInteraction
