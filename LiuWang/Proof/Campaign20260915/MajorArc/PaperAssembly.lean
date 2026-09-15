import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1.SourceSums

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.MajorArc

def paperOrdinaryKernel (N a q : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ)
    (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let M := principalCoefficient q * J N eta
    let R := ordinaryPacket N a q d e eta;
    -3 * M ^ 2 * R + 3 * M * R ^ 2 - R ^ 3

def paperOrdinaryIntegral (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    paperOrdinaryKernel N i.2 i.1 d e eta * arcPhase N i.2 i.1 eta

theorem continuous_paperOrdinaryKernel {N : ℕ} (hN : 0 < N)
    (a q : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) :
    Continuous (paperOrdinaryKernel N a q d e) := by
  by_cases hq : q = 0
  · subst q
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    have hJ := continuous_J hN
    have hR := ordinaryPacket_continuous (q := q) hN a d e
    unfold paperOrdinaryKernel
    simp only [dif_neg hq]
    fun_prop

theorem paperOrdinaryKernel_eq_interaction_of_not_dvd {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : Nat.Coprime a q)
    (hq : (q : ℝ) ≤ sourceP N) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) (hdq : ¬d.modulus ∣ q) (eta : ℝ) :
    paperOrdinaryKernel N a q d e eta = interactionKernel N a q eta := by
  simp only [paperOrdinaryKernel, dif_neg (NeZero.ne q), interactionKernel,
    packet_eq, zeroPacket_split_paper hN ha hq hd, if_neg hdq, add_zero]

theorem same_source_six_arcs_all_moduli {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    (∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
      ((principalCoefficient q * J N eta - zeroPacket q N a eta) ^ 3 -
        (principalCoefficient q * J N eta - ordinaryPacket N a q d e eta) ^ 3) *
          arcPhase N a q eta) =
      if d.modulus ∣ q then
        I15arc N q d e + I16arc N q d e + I17arc N q d e +
          I18arc N q d e + I19arc N q d e + I110arc N q d e
      else 0 := by
  by_cases hdq : d.modulus ∣ q
  · rw [if_pos hdq]
    exact same_source_six_arcs hN hq hd hdq
  · rw [if_neg hdq]
    apply Finset.sum_eq_zero
    intro a ha
    simp only [zeroPacket_split_paper hN (mem_numerators.mp ha).2.2 hq hd,
      if_neg hdq, add_zero, sub_self, zero_mul, intervalIntegral.integral_zero]

theorem interactionIntegral_sub_paperOrdinaryIntegral {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    interactionIntegral N - paperOrdinaryIntegral N d e =
      I15 N d e + I16 N d e + I17 N d e +
        I18 N d e + I19 N d e + I110 N d e := by
  rw [interactionIntegral, paperOrdinaryIntegral, ← Finset.sum_sub_distrib,
    coreIndices, Finset.sum_sigma]
  simp only [I15, I16, I17, I18, I19, I110, modulusSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hqs := (mem_denominators
    (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le q).mp hq
  have hq0 : q ≠ 0 := by omega
  let : NeZero q := ⟨hq0⟩
  simp only [dif_neg hq0]
  have heq :
      (∑ a ∈ numerators q,
        ((∫ eta in -deltaRadius N q..deltaRadius N q,
          interactionKernel N a q eta * arcPhase N a q eta) -
        (∫ eta in -deltaRadius N q..deltaRadius N q,
          paperOrdinaryKernel N a q d e eta * arcPhase N a q eta))) =
      ∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
        ((principalCoefficient q * J N eta - zeroPacket q N a eta) ^ 3 -
          (principalCoefficient q * J N eta - ordinaryPacket N a q d e eta) ^ 3) *
            arcPhase N a q eta := by
    apply Finset.sum_congr rfl
    intro a _
    have ho : IntervalIntegrable (fun eta =>
        paperOrdinaryKernel N a q d e eta * arcPhase N a q eta)
        volume (-deltaRadius N q) (deltaRadius N q) :=
      ((continuous_paperOrdinaryKernel (nat_pos_of_exp_le hN) a q d e).mul
        (continuous_arcPhase N a q)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub
      (interaction_integrable (nat_pos_of_exp_le hN) a q _ _)
      ho]
    congr 1
    ext eta
    simp only [interactionKernel, packet_eq, paperOrdinaryKernel, dif_neg hq0]
    ring
  rw [heq, same_source_six_arcs_all_moduli hN hqs.2 hd]
  split_ifs <;> simp

theorem interactionIntegral_paper_source_split {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    interactionIntegral N =
      paperOrdinaryIntegral N d e + I15 N d e + I16 N d e +
        I17 N d e + I18 N d e + I19 N d e + I110 N d e := by
  have h := interactionIntegral_sub_paperOrdinaryIntegral hN hd
  calc
    _ = paperOrdinaryIntegral N d e +
        (interactionIntegral N - paperOrdinaryIntegral N d e) := by ring
    _ = _ := by rw [h]; ring

theorem majorIntegral_paper_source_lower {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    0.65617 * (N : ℝ) ^ 2 + (paperOrdinaryIntegral N d e).re +
      (I15 N d e).re + (I16 N d e).re + (I17 N d e).re +
      (I18 N d e).re + (I19 N d e).re + (I110 N d e).re -
      6760 * (N : ℝ) ^ 2 / sourceL N ^ 4 ≤ (majorIntegral N).re := by
  have h := re_major_lower_strong hN hodd
  rw [interactionIntegral_paper_source_split hN hd] at h
  simp only [Complex.add_re] at h
  linarith

#print axioms interactionIntegral_paper_source_split
#print axioms majorIntegral_paper_source_lower

end LiuWang.Proof.Campaign20260915.MajorArc
