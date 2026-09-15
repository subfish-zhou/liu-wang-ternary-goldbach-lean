import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1.SixTerms

set_option autoImplicit false
noncomputable section
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1

theorem moebiusWeight_sq (q : ℕ) : moebiusWeight q ^ 2 = moebiusWeight q := by
  rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;>
    norm_num [moebiusWeight, h]

theorem I15_holder_cubic_constants {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) (hdq : d.modulus ∣ q) :
    ‖I15arc N q d e‖ ≤
      3 * moebiusWeight q * Real.sqrt d.modulus / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * principalRoot ^ 2 * exceptionalScale N e.re := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hn := nat_pos_of_exp_le hN
  have hp : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  obtain ⟨hpr, her, _⟩ := roots_pos hN' (NeZero.pos q)
  have he : 0 < exceptionalScale N e.re := mul_pos her (baseWeight_pos hn _)
  have h := cubicArc_bound hN (NeZero.pos q)
    (fun a => -3 * principalCoefficient q ^ 2 * exceptionalFactor a q d)
    (fun _ => J N) (fun _ => J N) (fun _ => Jrho N (e.re : ℂ))
    (D := 3 * (moebiusWeight q / q.totient) ^ 2 * (Real.sqrt d.modulus / q.totient))
    (by positivity) hpr hpr he
    (fun a ha => by
      simp only [norm_mul, norm_pow, norm_neg, Complex.norm_ofNat, norm_principalCoefficient]
      exact mul_le_mul_of_nonneg_left
        (exceptionalFactor_bound (mem_numerators.mp ha).2.2 d hdq) (by positivity))
    (fun _ _ => continuous_J hn) (fun _ _ => continuous_J hn)
    (fun _ _ => Jrho_continuous hn _)
    (fun _ _ => by simpa only [Jrho_one_eq_J] using
      principal_cubic_bound hn (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun _ _ => by simpa only [Jrho_one_eq_J] using
      principal_cubic_bound hn (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
  apply h.trans_eq
  rw [div_pow, moebiusWeight_sq]
  field_simp

theorem I18_holder_cubic_constants {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) (hdq : d.modulus ∣ q) :
    ‖I18arc N q d e‖ ≤
      3 * moebiusWeight q * d.modulus / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * principalRoot * exceptionalScale N e.re ^ 2 := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hn := nat_pos_of_exp_le hN
  have hp : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  obtain ⟨hpr, her, _⟩ := roots_pos hN' (NeZero.pos q)
  have he : 0 < exceptionalScale N e.re := mul_pos her (baseWeight_pos hn _)
  have h := cubicArc_bound hN (NeZero.pos q)
    (fun a => 3 * principalCoefficient q * exceptionalFactor a q d ^ 2)
    (fun _ => J N) (fun _ => Jrho N (e.re : ℂ)) (fun _ => Jrho N (e.re : ℂ))
    (D := 3 * (moebiusWeight q / q.totient) * (Real.sqrt d.modulus / q.totient) ^ 2)
    (by have := moebiusWeight_nonneg q; positivity) hpr he he
    (fun a ha => by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat, norm_principalCoefficient]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _)
          (exceptionalFactor_bound (mem_numerators.mp ha).2.2 d hdq) 2)
        (mul_nonneg (by norm_num) (principalMass_nonneg q)))
    (fun _ _ => continuous_J hn) (fun _ _ => Jrho_continuous hn _)
    (fun _ _ => Jrho_continuous hn _)
    (fun _ _ => by simpa only [Jrho_one_eq_J] using
      principal_cubic_bound hn (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
  apply h.trans_eq
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg d.modulus)]
  field_simp

theorem I110_holder_cubic_constants {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) (hdq : d.modulus ∣ q) :
    ‖I110arc N q d e‖ ≤
      (d.modulus * Real.sqrt d.modulus) / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * exceptionalScale N e.re ^ 3 := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hn := nat_pos_of_exp_le hN
  have hp : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have he : 0 < exceptionalScale N e.re :=
    mul_pos (roots_pos hN' (NeZero.pos q)).2.1 (baseWeight_pos hn _)
  have h := cubicArc_bound hN (NeZero.pos q)
    (fun a => -(exceptionalFactor a q d ^ 3))
    (fun _ => Jrho N (e.re : ℂ)) (fun _ => Jrho N (e.re : ℂ))
    (fun _ => Jrho N (e.re : ℂ))
    (D := (Real.sqrt d.modulus / q.totient) ^ 3) (by positivity) he he he
    (fun a ha => by
      simp only [norm_neg, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (exceptionalFactor_bound (mem_numerators.mp ha).2.2 d hdq) 3)
    (fun _ _ => Jrho_continuous hn _) (fun _ _ => Jrho_continuous hn _)
    (fun _ _ => Jrho_continuous hn _)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
    (fun _ _ => exceptional_cubic_bound hn (exceptional_beta_ge_09957 hN hd)
      hd.2.2.2.1.le (deltaRadius_pos hN' (NeZero.pos q)).le)
  apply h.trans_eq
  rw [div_pow, pow_succ (Real.sqrt (d.modulus : ℝ)) 2,
    Real.sq_sqrt (Nat.cast_nonneg d.modulus)]
  field_simp

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1
