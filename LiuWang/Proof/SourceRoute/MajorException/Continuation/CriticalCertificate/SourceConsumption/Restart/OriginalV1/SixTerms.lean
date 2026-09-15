import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1.MixedTerms

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularIntegral LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1

theorem paper_induced_mem_T_iff {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    e ∈ zeroValues (inducedAt d q) (sourceT N) ↔ d.modulus ∣ q := by
  rw [← paper_induced_mem_iff hN hq hd]
  simp only [mem_zeroValues, hd.2.2.1, abs_zero]
  have ho := (omegaCutoff_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)).le
  have ht := ho.trans (omegaCutoff_le_sourceT (q := q) hN)
  simp only [ho, ht, true_and]

theorem zeroPacket_split_paper {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : Nat.Coprime a q)
    (hq : (q : ℝ) ≤ sourceP N) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) (eta : ℝ) :
    zeroPacket q N a eta = ordinaryPacket N a q d e eta +
      if d.modulus ∣ q then exceptionalFactor a q d * Jrho N (e.re : ℂ) eta else 0 := by
  have he : (e.re : ℂ) = e := by
    apply Complex.ext <;> simp [hd.2.2.1]
  rw [zeroPacket_eq_all_values N a eta ha]
  have h := sum_split_retained (q := q) (sourceT N) d e
    (fun chi rho => G a chi * ((zeroMultiplicity chi rho : ℂ) * Jrho N rho eta))
  simp only [paper_induced_mem_T_iff hN hq hd, ← Finset.mul_sum] at h
  have hh := congrArg (fun z : ℂ => (q.totient : ℂ)⁻¹ * z) h
  by_cases hdq : d.modulus ∣ q
  · simpa only [ordinaryPacket, zeroValueSum, zeroMultiplicity, exceptionalFactor, he,
      if_pos hdq, show analyticOrderNatAt (inducedAt d q).LFunction e = 1 from
        paper_source_multiplicity hN hd hdq, Nat.cast_one, one_mul,
      mul_add, mul_assoc] using hh
  · simpa only [ordinaryPacket, zeroValueSum, zeroMultiplicity,
      if_neg hdq, add_zero] using hh

def I15arc (N q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  cubicArc N q (fun a => -3 * principalCoefficient q ^ 2 * exceptionalFactor a q d)
    (fun _ => J N) (fun _ => J N) (fun _ => Jrho N (e.re : ℂ))

def I18arc (N q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  cubicArc N q (fun a => 3 * principalCoefficient q * exceptionalFactor a q d ^ 2)
    (fun _ => J N) (fun _ => Jrho N (e.re : ℂ)) (fun _ => Jrho N (e.re : ℂ))

def I110arc (N q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  cubicArc N q (fun a => -(exceptionalFactor a q d ^ 3))
    (fun _ => Jrho N (e.re : ℂ)) (fun _ => Jrho N (e.re : ℂ))
    (fun _ => Jrho N (e.re : ℂ))

theorem same_source_six_kernels {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : Nat.Coprime a q)
    (hq : (q : ℝ) ≤ sourceP N) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) (hdq : d.modulus ∣ q) (eta : ℝ) :
    let M := principalCoefficient q * J N eta
    let E := exceptionalFactor a q d * Jrho N (e.re : ℂ) eta
    let R := ordinaryPacket N a q d e eta
    (M - zeroPacket q N a eta) ^ 3 - (M - R) ^ 3 =
      -3 * M ^ 2 * E + 6 * M * E * R - 3 * E * R ^ 2 +
        3 * M * E ^ 2 - 3 * E ^ 2 * R - E ^ 3 := by
  dsimp
  rw [zeroPacket_split_paper hN ha hq hd, if_pos hdq]
  ring

theorem same_source_six_arcs {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdq : d.modulus ∣ q) :
    (∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
      ((principalCoefficient q * J N eta - zeroPacket q N a eta) ^ 3 -
        (principalCoefficient q * J N eta - ordinaryPacket N a q d e eta) ^ 3) *
          arcPhase N a q eta) =
      I15arc N q d e + I16arc N q d e + I17arc N q d e +
        I18arc N q d e + I19arc N q d e + I110arc N q d e := by
  have hn := nat_pos_of_exp_le hN
  simp only [I15arc, I16arc, I17arc, I18arc, I19arc, I110arc, cubicArc,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hj := continuous_J hn
  have he := Jrho_continuous hn (e.re : ℂ)
  have hr := ordinaryPacket_continuous (q := q) hn a d e
  have hp := continuous_arcPhase N a q
  have hint (f : ℝ → ℂ) (hf : Continuous f) :
      IntervalIntegrable f volume (-deltaRadius N q) (deltaRadius N q) :=
    hf.intervalIntegrable _ _
  simp_rw [same_source_six_kernels hN (mem_numerators.mp ha).2.2 hq hd hdq]
  simp only [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop)),
    ← intervalIntegral.integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop)),
    ← intervalIntegral.integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop)),
    ← intervalIntegral.integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop)),
    ← intervalIntegral.integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop))]
  congr 1
  ext eta
  ring

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1
