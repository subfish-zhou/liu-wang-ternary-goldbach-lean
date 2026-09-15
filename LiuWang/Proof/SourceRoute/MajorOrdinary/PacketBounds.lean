import LiuWang.Proof.SourceRoute.MajorOrdinary.CubicNorm
import LiuWang.Proof.WeightedLowZeros.Weight

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical MeasureTheory Set
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.SourceRoute.MajorOrdinary

def arcZeroWeight (N q : ℕ) (rho : ℂ) : ℝ :=
  if |rho.im| ≤ omegaCutoff N q then WeightedLowZeros.weight N rho.re
  else 5 * ((N : ℝ) ^ (rho.re - 1) / |rho.im|)

def lowWeightSum (N q : ℕ) [NeZero q] : ℝ :=
  ∑ chi : Character q,
    ∑ rho ∈ (zeroValues chi (sourceT N)).filter (fun rho => |rho.im| ≤ omegaCutoff N q),
      (analyticOrderNatAt chi.LFunction rho : ℝ) * WeightedLowZeros.weight N rho.re

def highWeightSum (N q : ℕ) [NeZero q] : ℝ :=
  ∑ chi : Character q,
    ∑ rho ∈ (zeroValues chi (sourceT N)).filter (fun rho => omegaCutoff N q < |rho.im|),
      (analyticOrderNatAt chi.LFunction rho : ℝ) *
        ((N : ℝ) ^ (rho.re - 1) / |rho.im|)

def zeroEnvelope (N q : ℕ) [NeZero q] : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ zeroValues chi (sourceT N),
    (analyticOrderNatAt chi.LFunction rho : ℝ) * arcZeroWeight N q rho

theorem arcZeroWeight_nonneg (N q : ℕ) {rho : ℂ} (hb : 0 < rho.re) :
    0 ≤ arcZeroWeight N q rho := by
  unfold arcZeroWeight
  split_ifs
  · exact WeightedLowZeros.weight_nonneg N hb
  · positivity

theorem zeroEnvelope_nonneg (N q : ℕ) [NeZero q] : 0 ≤ zeroEnvelope N q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ hr =>
    mul_nonneg (Nat.cast_nonneg _) (arcZeroWeight_nonneg N q (mem_zeroValues.mp hr).2.1)

theorem zeroEnvelope_split (N q : ℕ) [NeZero q] :
    zeroEnvelope N q = lowWeightSum N q + 5 * highWeightSum N q := by
  simp only [zeroEnvelope, lowWeightSum, highWeightSum, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  by_cases h : |rho.im| ≤ omegaCutoff N q
  · simp [arcZeroWeight, h, not_lt.mpr h]
  · simp [arcZeroWeight, h, lt_of_not_ge h]
    ring

theorem Jrho_le_arcZeroWeight {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {rho : ℂ} (hb : 0 < rho.re) {eta : ℝ} (he : |eta| ≤ deltaRadius N q) :
    ‖Jrho N rho eta‖ ≤ (N : ℝ) * arcZeroWeight N q rho := by
  unfold arcZeroWeight
  split_ifs with hg
  · exact WeightedLowZeros.Jrho_le_weight (nat_pos_of_exp_le hN) hb eta
  · have hw : omegaCutoff N q < |rho.im| := lt_of_not_ge hg
    have hi : rho.im ≠ 0 := abs_pos.mp ((omegaCutoff_pos hN hq).trans hw)
    have heta : |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ)) := by
      rw [deltaRadius_eq_omega] at he
      exact he.trans (div_le_div_of_nonneg_right hw.le (by positivity))
    apply (OscillatoryBounds.Jrho_near (nat_pos_of_exp_le hN) hb.le hi heta).trans_eq
    rw [Real.rpow_sub_one (natCast_pos_of_exp_le hN).ne']
    field_simp [(natCast_pos_of_exp_le hN).ne']

theorem zeroValueSum_le_envelope {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q)
    {eta : ℝ} (he : |eta| ≤ deltaRadius N q) :
    ‖zeroValueSum chi N (sourceT N) eta‖ ≤
      (N : ℝ) * ∑ rho ∈ zeroValues chi (sourceT N),
        (analyticOrderNatAt chi.LFunction rho : ℝ) * arcZeroWeight N q rho := by
  rw [zeroValueSum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro rho hr
  rw [norm_mul, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left
    (Jrho_le_arcZeroWeight hN (NeZero.pos q) (mem_zeroValues.mp hr).2.1 he)
    (Nat.cast_nonneg _)).trans_eq
  ring

def packetBound (N q : ℕ) [NeZero q] : ℝ :=
  (Real.sqrt (q : ℝ) / (q.totient : ℝ)) * (N : ℝ) * zeroEnvelope N q

theorem packetBound_nonneg (N q : ℕ) [NeZero q] : 0 ≤ packetBound N q := by
  unfold packetBound
  exact mul_nonneg (by positivity) (zeroEnvelope_nonneg N q)

theorem packet_le_bound {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (ha : Nat.Coprime a q)
    {eta : ℝ} (he : |eta| ≤ deltaRadius N q) :
    ‖packet N a q eta‖ ≤ packetBound N q := by
  have hg (chi : Character q) : ‖G a chi‖ ≤ Real.sqrt (q : ℝ) :=
    (norm_G_le_sqrt_conductor ha chi).trans
      (Real.sqrt_le_sqrt (by exact_mod_cast
        BombieriVinogradov.DirichletCharacter.conductor_le_level chi))
  rw [packet_eq, zeroPacket_eq_all_values N a eta ha, norm_mul, norm_inv,
    Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ *
        ∑ chi : Character q, ‖G a chi * zeroValueSum chi N (sourceT N) eta‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q,
        Real.sqrt (q : ℝ) * ((N : ℝ) *
          ∑ rho ∈ zeroValues chi (sourceT N),
            (analyticOrderNatAt chi.LFunction rho : ℝ) * arcZeroWeight N q rho) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      exact mul_le_mul (hg chi) (zeroValueSum_le_envelope hN chi he)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      simp only [packetBound, zeroEnvelope, ← Finset.mul_sum]
      ring

theorem cubicMass_packet {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (ha : Nat.Coprime a q) :
    cubicMass (deltaRadius N q) (packet N a q) ≤
      2 * deltaRadius N q * packetBound N q ^ 3 := by
  apply cubicMass_le_const (deltaRadius_pos hN (NeZero.pos q)).le
    (continuous_packet (nat_pos_of_exp_le hN) a q)
  intro eta he
  exact packet_le_bound hN ha (abs_le.mpr he)

theorem cubicMass_Jrho_low {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {rho : ℂ} (hb : 0 < rho.re) :
    cubicMass (deltaRadius N q) (Jrho N rho) ≤
      2 * deltaRadius N q * ((N : ℝ) * WeightedLowZeros.weight N rho.re) ^ 3 :=
  cubicMass_le_const (deltaRadius_pos hN hq).le
    (SingularIntegral.Jrho_continuous (nat_pos_of_exp_le hN) rho)
    (fun eta _ => WeightedLowZeros.Jrho_le_weight (nat_pos_of_exp_le hN) hb eta)

theorem cubicMass_Jrho_high {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {rho : ℂ} (hb : 0 < rho.re) (hg : omegaCutoff N q < |rho.im|) :
    cubicMass (deltaRadius N q) (Jrho N rho) ≤
      2 * deltaRadius N q *
        ((N : ℝ) * (5 * ((N : ℝ) ^ (rho.re - 1) / |rho.im|))) ^ 3 := by
  apply cubicMass_le_const (deltaRadius_pos hN hq).le
    (SingularIntegral.Jrho_continuous (nat_pos_of_exp_le hN) rho)
  intro eta he
  simpa only [arcZeroWeight, if_neg (not_le.mpr hg)] using
    Jrho_le_arcZeroWeight hN hq hb (abs_le.mpr he)

end LiuWang.Proof.SourceRoute.MajorOrdinary
