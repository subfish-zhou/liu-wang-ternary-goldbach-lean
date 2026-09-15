import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1.Holder
import LiuWang.Proof.SourceRoute.MajorException.PureTerms
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.MixedFinite

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularIntegral LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.SourceRoute.MajorException
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1

def exceptionalFactor (a q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum) : ℂ :=
  (q.totient : ℂ)⁻¹ * G a (inducedAt d q)

theorem exceptionalFactor_bound {a q : ℕ} [NeZero q] (ha : Nat.Coprime a q)
    (d : PrimitiveQuadraticDatum) (hdq : d.modulus ∣ q) :
    ‖exceptionalFactor a q d‖ ≤ Real.sqrt d.modulus / q.totient := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have hc : (inducedAt d q).conductor = d.modulus := by
    rw [inducedAt, dif_pos hdq, DirichletCharacter.conductor_changeLevel, d.isPrimitive]
  rw [exceptionalFactor, norm_mul, norm_inv, Complex.norm_natCast]
  have h := mul_le_mul_of_nonneg_left (norm_G_le_sqrt_conductor ha (inducedAt d q))
    (show (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ by positivity)
  simpa only [hc, div_eq_mul_inv, mul_comm] using h

def I16arc (N q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  cubicArc N q (fun a => 6 * principalCoefficient q * exceptionalFactor a q d)
    (fun _ => J N) (fun _ => Jrho N (e.re : ℂ)) (fun a => ordinaryPacket N a q d e)

def I17arc (N q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  cubicArc N q (fun a => -3 * exceptionalFactor a q d)
    (fun _ => Jrho N (e.re : ℂ)) (fun a => ordinaryPacket N a q d e)
    (fun a => ordinaryPacket N a q d e)

def I19arc (N q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  cubicArc N q (fun a => -3 * exceptionalFactor a q d ^ 2)
    (fun _ => Jrho N (e.re : ℂ)) (fun _ => Jrho N (e.re : ℂ))
    (fun a => ordinaryPacket N a q d e)

theorem I16_holder {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) (hdq : d.modulus ∣ q) {M : ℝ}
    (hM : 0 < M) (hm : ordinaryMass N q d e ≤ M) :
    ‖I16arc N q d e‖ ≤
      6 * moebiusWeight q * Real.sqrt d.modulus * Real.sqrt q / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * principalRoot * exceptionalScale N e.re * radiusRoot N q * M := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hn := nat_pos_of_exp_le hN
  have hp : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  obtain ⟨hpr, her, hrr⟩ := roots_pos hN' (NeZero.pos q)
  have he : 0 < exceptionalScale N e.re :=
    mul_pos her (baseWeight_pos hn _)
  have hr : 0 < Real.sqrt q / q.totient * radiusRoot N q * M := by
    have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos q))
    positivity
  have h := cubicArc_bound hN (NeZero.pos q)
    (fun a => 6 * principalCoefficient q * exceptionalFactor a q d)
    (fun _ => J N) (fun _ => Jrho N (e.re : ℂ)) (fun a => ordinaryPacket N a q d e)
    (D := 6 * (moebiusWeight q / q.totient) * (Real.sqrt d.modulus / q.totient))
    (by have := moebiusWeight_nonneg q; positivity) hpr he hr
    (fun a ha => by
      simp only [norm_mul, Complex.norm_ofNat, norm_principalCoefficient]
      exact mul_le_mul_of_nonneg_left
        (exceptionalFactor_bound (mem_numerators.mp ha).2.2 d hdq)
        (mul_nonneg (by norm_num) (principalMass_nonneg q)))
    (fun _ _ => continuous_J hn) (fun _ _ => Jrho_continuous hn _)
    (fun a _ => ordinaryPacket_continuous hn a d e)
    (fun _ _ => by simpa only [Jrho_one_eq_J] using
      principal_cubic_bound hn (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun a ha => ordinaryPacket_cubic hN (mem_numerators.mp ha).2.2 d e hm)
  apply h.trans_eq
  field_simp

theorem I17_holder {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) (hdq : d.modulus ∣ q) {M : ℝ}
    (hM : 0 < M) (hm : ordinaryMass N q d e ≤ M) :
    ‖I17arc N q d e‖ ≤
      3 * Real.sqrt d.modulus * q / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * exceptionalScale N e.re * radiusRoot N q ^ 2 * M ^ 2 := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hn := nat_pos_of_exp_le hN
  have hp : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  obtain ⟨_, her, hrr⟩ := roots_pos hN' (NeZero.pos q)
  have he : 0 < exceptionalScale N e.re := mul_pos her (baseWeight_pos hn _)
  have hr : 0 < Real.sqrt q / q.totient * radiusRoot N q * M := by
    have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos q))
    positivity
  have h := cubicArc_bound hN (NeZero.pos q)
    (fun a => -3 * exceptionalFactor a q d)
    (fun _ => Jrho N (e.re : ℂ)) (fun a => ordinaryPacket N a q d e)
    (fun a => ordinaryPacket N a q d e)
    (D := 3 * (Real.sqrt d.modulus / q.totient)) (by positivity) he hr hr
    (fun a ha => by
      simp only [norm_mul, norm_neg, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left
        (exceptionalFactor_bound (mem_numerators.mp ha).2.2 d hdq) (by norm_num))
    (fun _ _ => Jrho_continuous hn _)
    (fun a _ => ordinaryPacket_continuous hn a d e)
    (fun a _ => ordinaryPacket_continuous hn a d e)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun a ha => ordinaryPacket_cubic hN (mem_numerators.mp ha).2.2 d e hm)
    (fun a ha => ordinaryPacket_cubic hN (mem_numerators.mp ha).2.2 d e hm)
  apply h.trans_eq
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg q)]

theorem I19_holder {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) (hdq : d.modulus ∣ q) {M : ℝ}
    (hM : 0 < M) (hm : ordinaryMass N q d e ≤ M) :
    ‖I19arc N q d e‖ ≤
      3 * d.modulus * Real.sqrt q / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * exceptionalScale N e.re ^ 2 * radiusRoot N q * M := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hn := nat_pos_of_exp_le hN
  have hp : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  obtain ⟨_, her, hrr⟩ := roots_pos hN' (NeZero.pos q)
  have he : 0 < exceptionalScale N e.re := mul_pos her (baseWeight_pos hn _)
  have hr : 0 < Real.sqrt q / q.totient * radiusRoot N q * M := by
    have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos q))
    positivity
  have h := cubicArc_bound hN (NeZero.pos q)
    (fun a => -3 * exceptionalFactor a q d ^ 2)
    (fun _ => Jrho N (e.re : ℂ)) (fun _ => Jrho N (e.re : ℂ))
    (fun a => ordinaryPacket N a q d e)
    (D := 3 * (Real.sqrt d.modulus / q.totient) ^ 2) (by positivity) he he hr
    (fun a ha => by
      simp only [norm_mul, norm_pow, norm_neg, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _)
          (exceptionalFactor_bound (mem_numerators.mp ha).2.2 d hdq) 2) (by norm_num))
    (fun _ _ => Jrho_continuous hn _) (fun _ _ => Jrho_continuous hn _)
    (fun a _ => ordinaryPacket_continuous hn a d e)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun a ha => ordinaryPacket_cubic hN (mem_numerators.mp ha).2.2 d e hm)
  apply h.trans_eq
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg d.modulus)]
  field_simp

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1
