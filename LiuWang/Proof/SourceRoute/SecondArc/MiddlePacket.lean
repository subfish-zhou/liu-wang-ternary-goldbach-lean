import LiuWang.Proof.SourceRoute.SecondArc.AlphaIntegral
import LiuWang.Proof.OscillatoryBounds.StrongConsumer
import LiuWang.Proof.CharacterExpansion.GaussInduction

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc

def middlePacket (N q a : ℕ) [NeZero q] (u v eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q,
    LiuWang.Proof.CharacterExpansion.G a chi *
      ∑ rho ∈ bandValues chi (1 / 2) u v,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem middlePacket_eq_complete (N q a : ℕ) [NeZero q] (u v eta : ℝ) :
    middlePacket N q a u v eta =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q,
        LiuWang.Proof.CharacterExpansion.G a chi *
          ∑ rho ∈ (LiuWang.Proof.CompleteExpansion.zeroValues chi v).filter
            (fun rho => u ≤ |rho.im|),
              (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  simp only [middlePacket, bandValues, Applications.half_values_eq_complete]

theorem norm_middlePacket_le_weighted {N q a : ℕ} [NeZero q]
    (hN : 0 < N) (ha : Nat.Coprime a q) {u : ℝ} (hu : 0 < u) (v eta : ℝ) :
    ‖middlePacket N q a u v eta‖ ≤
      (10 * (N : ℝ) * Real.sqrt q / q.totient) *
        (∑ chi : Character q, ∑ rho ∈ bandValues chi (1 / 2) u v,
          ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
            (0.001 * (N : ℝ)) ^ (rho.re - 1)) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hg (chi : Character q) : ‖LiuWang.Proof.CharacterExpansion.G a chi‖ ≤
      Real.sqrt q :=
    (LiuWang.Proof.CharacterExpansion.norm_G_le_sqrt_conductor ha chi).trans
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr
        (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)))
  have hk (chi : Character q) (rho : ℂ) (hr : rho ∈ bandValues chi (1 / 2) u v) :
      ‖Jrho N rho eta‖ ≤
        10 * (N : ℝ) * (0.001 * (N : ℝ)) ^ (rho.re - 1) / Real.sqrt |rho.im| := by
    have hz := mem_bandValues.mp hr
    have him : rho.im ≠ 0 := abs_pos.mp (hu.trans_le hz.2.2.2)
    apply (LiuWang.Proof.OscillatoryBounds.Jrho_sqrt_ten hN hz.2.1.2.1.le him eta).trans_eq
    rw [Real.mul_rpow (by norm_num) hn.le, Real.rpow_sub_one hn.ne']
    field_simp
  rw [middlePacket, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ *
        ∑ chi : Character q, Real.sqrt q *
          ∑ rho ∈ bandValues chi (1 / 2) u v,
            10 * (N : ℝ) *
              (((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
                (0.001 * (N : ℝ)) ^ (rho.re - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      apply mul_le_mul (hg chi) _ (norm_nonneg _) (Real.sqrt_nonneg _)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro rho hr
      rw [norm_mul, Complex.norm_natCast]
      exact (mul_le_mul_of_nonneg_left (hk chi rho hr) (Nat.cast_nonneg _)).trans_eq
        (by ring)
    _ = _ := by simp only [Finset.mul_sum]; ring

/-- Equation (5.3) on the actual signed packet, using the stronger frozen constant 10. -/
theorem norm_middlePacket_le_alpha_integrals {N q a : ℕ} [NeZero q]
    (hN : 0 < N) (ha : Nat.Coprime a q) {u : ℝ} (hu : 0 < u) (v eta : ℝ) :
    ‖middlePacket N q a u v eta‖ ≤
      (10 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((0.001 * (N : ℝ)) ^ (-(1 / 2) : ℝ) * bandMass q (1 / 2) u v +
          (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
            alphaKernel (0.001 * (N : ℝ)) alpha * bandMass q alpha u v) +
          ∫ alpha in (59 / 60 : ℝ)..1,
            alphaKernel (0.001 * (N : ℝ)) alpha * bandMass q alpha u v) := by
  have h := norm_middlePacket_le_weighted hN ha hu v eta
  rw [band_weight_alpha_split (by positivity : 0 < 0.001 * (N : ℝ))
    (by norm_num : (1 / 2 : ℝ) ≤ 59 / 60) (by norm_num : (59 / 60 : ℝ) ≤ 1)] at h
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num] at h
  exact h

end LiuWang.Proof.SourceRoute.SecondArc
