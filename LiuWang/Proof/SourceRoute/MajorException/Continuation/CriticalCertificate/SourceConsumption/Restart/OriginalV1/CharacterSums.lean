import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1.SourceSums

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.WeightedLowZeros

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1

theorem all_characters_card (q : ℕ) [NeZero q] :
    Fintype.card (Character q) = q.totient := by
  simpa only [Nat.card_eq_fintype_card] using
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

theorem ordinaryPacket_square (N a q : ℕ) [NeZero q]
    (d : PrimitiveQuadraticDatum) (e : ℂ) (eta : ℝ) :
    ordinaryPacket N a q d e eta ^ 2 =
      (q.totient : ℂ)⁻¹ ^ 2 *
        ∑ chi : Character q, ∑ psi : Character q, G a chi * G a psi *
          ∑ rho ∈ retainedValues chi (sourceT N) d e,
            ∑ sigma ∈ retainedValues psi (sourceT N) d e,
              (zeroMultiplicity chi rho : ℂ) * (zeroMultiplicity psi sigma : ℂ) *
                Jrho N rho eta * Jrho N sigma eta := by
  unfold ordinaryPacket
  rw [mul_pow, pow_two (∑ chi : Character q, G a chi *
    ∑ rho ∈ retainedValues chi (sourceT N) d e,
      (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta), Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro psi _
  calc
    _ = G a chi * G a psi *
        ((∑ rho ∈ retainedValues chi (sourceT N) d e,
          (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta) *
        (∑ sigma ∈ retainedValues psi (sourceT N) d e,
          (zeroMultiplicity psi sigma : ℂ) * Jrho N sigma eta)) := by ring
    _ = _ := by
      rw [Finset.sum_mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro rho _
      apply Finset.sum_congr rfl
      intro sigma _
      ring

theorem I16_pointwise_character_sum (N a q : ℕ) [NeZero q]
    (d : PrimitiveQuadraticDatum) (e : ℂ) (eta : ℝ) :
    6 * (CompleteExpansion.principalCoefficient q * J N eta) *
      (exceptionalFactor a q d * Jrho N (e.re : ℂ) eta) * ordinaryPacket N a q d e eta =
      (6 * CompleteExpansion.principalCoefficient q * (q.totient : ℂ)⁻¹ ^ 2) *
        ∑ chi : Character q, G a (inducedAt d q) * G a chi *
          ∑ rho ∈ retainedValues chi (sourceT N) d e,
            (zeroMultiplicity chi rho : ℂ) *
              (J N eta * Jrho N (e.re : ℂ) eta * Jrho N rho eta) := by
  simp only [ordinaryPacket, exceptionalFactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  ring

theorem I17_pointwise_character_sum (N a q : ℕ) [NeZero q]
    (d : PrimitiveQuadraticDatum) (e : ℂ) (eta : ℝ) :
    -3 * (exceptionalFactor a q d * Jrho N (e.re : ℂ) eta) *
      ordinaryPacket N a q d e eta ^ 2 =
      (-3 * (q.totient : ℂ)⁻¹ ^ 3) *
        ∑ chi : Character q, ∑ psi : Character q,
          G a (inducedAt d q) * G a chi * G a psi *
            ∑ rho ∈ retainedValues chi (sourceT N) d e,
              ∑ sigma ∈ retainedValues psi (sourceT N) d e,
                (zeroMultiplicity chi rho : ℂ) * (zeroMultiplicity psi sigma : ℂ) *
                  (Jrho N (e.re : ℂ) eta * Jrho N rho eta * Jrho N sigma eta) := by
  rw [ordinaryPacket_square]
  simp only [exceptionalFactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro psi _
  apply Finset.sum_congr rfl
  intro rho _
  apply Finset.sum_congr rfl
  intro sigma _
  ring

theorem I19_pointwise_character_sum (N a q : ℕ) [NeZero q]
    (d : PrimitiveQuadraticDatum) (e : ℂ) (eta : ℝ) :
    -3 * (exceptionalFactor a q d * Jrho N (e.re : ℂ) eta) ^ 2 *
      ordinaryPacket N a q d e eta =
      (-3 * (q.totient : ℂ)⁻¹ ^ 3) *
        ∑ chi : Character q, G a (inducedAt d q) ^ 2 * G a chi *
          ∑ rho ∈ retainedValues chi (sourceT N) d e,
            (zeroMultiplicity chi rho : ℂ) *
              (Jrho N (e.re : ℂ) eta ^ 2 * Jrho N rho eta) := by
  simp only [ordinaryPacket, exceptionalFactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  ring

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1
