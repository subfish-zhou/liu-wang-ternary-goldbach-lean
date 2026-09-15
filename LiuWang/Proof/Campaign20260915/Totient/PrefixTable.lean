import LiuWang.Proof.Campaign20260915.Totient.RationalLog
import LiuWang.Proof.Campaign20260915.Totient.PrimorialReduction
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace LiuWang.Proof.Campaign20260915.Totient

def thetaLo (n : ℕ) : ℚ := ∑ p ∈ Nat.primesLE n, logLo p
def thetaHi (n : ℕ) : ℚ := ∑ p ∈ Nat.primesLE n, logHi p
def prefixEuler (n : ℕ) : ℚ := ∏ p ∈ Nat.primesLE n, (p : ℚ) / (p - 1)

def prefixCertificate (n : ℕ) : Prop :=
  1 ≤ thetaLo n ∧ 1 ≤ thetaHi n ∧ 0 < logLo (thetaLo n) ∧
    prefixEuler n ≤ (178107239 / 100000000 : ℚ) * logLo (thetaLo n) +
      (250637 / 100000 : ℚ) / logHi (thetaHi n)

instance (n : ℕ) : Decidable (prefixCertificate n) := inferInstanceAs
  (Decidable (1 ≤ thetaLo n ∧ 1 ≤ thetaHi n ∧ 0 < logLo (thetaLo n) ∧
    prefixEuler n ≤ (178107239 / 100000000 : ℚ) * logLo (thetaLo n) +
      (250637 / 100000 : ℚ) / logHi (thetaHi n)))

theorem rs_prefix_certificates :
    ∀ p ∈ Finset.range 314, 7 ≤ p → p.Prime → prefixCertificate p := by
  decide +kernel

theorem theta_313_certificate : (294 : ℚ) < thetaLo 313 := by
  decide +kernel

noncomputable section

open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

theorem theta_rational_bounds (n : ℕ) :
    (thetaLo n : ℝ) ≤ Chebyshev.theta n ∧ Chebyshev.theta n ≤ (thetaHi n : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  unfold thetaLo thetaHi
  push_cast
  constructor
  · apply Finset.sum_le_sum
    intro p hp
    exact (rational_log_bounds (by
      exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)).1
  · apply Finset.sum_le_sum
    intro p hp
    exact (rational_log_bounds (by
      exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)).2

theorem prefixEuler_eq_totient_ratio (n : ℕ) :
    (prefixEuler n : ℝ) = (primorial n : ℝ) / ((primorial n).totient : ℝ) := by
  have hpos : 0 < primorial n :=
    Finset.prod_pos (fun p hp => (Nat.mem_primesLE.mp hp).2.pos)
  have hsupport : (primorial n).primeFactors = Nat.primesLE n := by
    apply Nat.primeFactors_prod
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2
  rw [LiuWang.Proof.SourceRoute.ThirdArc.Continuation.totient_ratio_product hpos,
    hsupport]
  unfold prefixEuler
  push_cast
  rfl

theorem primorial_RS_of_prime_le_313 {p : ℕ} (hp : p.Prime)
    (h7 : 7 ≤ p) (h313 : p ≤ 313) :
    (primorial p : ℝ) / ((primorial p).totient : ℝ) ≤ nu (primorial p) := by
  have hc := rs_prefix_certificates p (Finset.mem_range.mpr (by omega)) h7 hp
  obtain ⟨hlo, hhi, hpos, hcert⟩ := hc
  have ht := theta_rational_bounds p
  have ht0 : 0 < (thetaLo p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hlo)
  have htheta := Chebyshev.theta_eq_log_primorial (p : ℝ)
  simp only [Nat.floor_natCast] at htheta
  have hll := (rational_log_bounds hlo).1.trans
    (Real.log_le_log ht0 ht.1)
  have hlh := (Real.log_le_log (ht0.trans_le ht.1) ht.2).trans
    (rational_log_bounds hhi).2
  rw [htheta] at hll hlh
  rw [← prefixEuler_eq_totient_ratio]
  apply (Rat.cast_le.mpr hcert).trans
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div] using
    nu_lower_from_log_bounds hpos hll hlh

theorem theta_313_gt_294 : (294 : ℝ) < Chebyshev.theta 313 :=
  (Rat.cast_lt.mpr theta_313_certificate).trans_le (theta_rational_bounds 313).1

#print axioms rs_prefix_certificates
#print axioms primorial_RS_of_prime_le_313
#print axioms theta_313_gt_294

end
end LiuWang.Proof.Campaign20260915.Totient
