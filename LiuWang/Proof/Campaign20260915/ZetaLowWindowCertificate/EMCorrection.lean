import LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate.PhaseSignStability

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

open LiuWang.Proof.Campaign20260915.ZetaValidation

def emTailFactor (s : ℂ) (N m : ℕ) : ℂ :=
  (N : ℂ) / (s - 1) - 1 / 2 +
    ∑ j ∈ range m, risingProduct s (j + 1) *
      ((bernoulli (j + 2) : ℂ) / (j + 2).factorial) / (N : ℂ) ^ (j + 1)

theorem eulerMaclaurinApprox_factored {N : ℕ} (hN : 1 ≤ N) (s : ℂ) (m : ℕ) :
    eulerMaclaurinApprox s N m =
      zetaPartialSum s N + (N : ℂ) ^ (-s) * emTailFactor s N m := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hp : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hNc, cpow_one]
  have hs : ∑ j ∈ range m, risingProduct s (j + 1) *
        ((bernoulli (j + 2) : ℂ) / (j + 2).factorial) *
          (N : ℂ) ^ (-s - (j + 1 : ℕ)) =
      (N : ℂ) ^ (-s) * ∑ j ∈ range m, risingProduct s (j + 1) *
        ((bernoulli (j + 2) : ℂ) / (j + 2).factorial) / (N : ℂ) ^ (j + 1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [cpow_sub _ _ hNc, cpow_natCast]
    ring
  rw [eulerMaclaurinApprox_eq_sum, hs]
  unfold abelApprox emTailFactor
  rw [hp]
  ring

theorem rotated_em_factored {N : ℕ} (hN : 1 ≤ N) (t : ℝ) (m : ℕ) (p : ℂ) :
    (eulerMaclaurinApprox (criticalPoint t) N m * p).re =
      (zetaPartialSum (criticalPoint t) N * p).re +
        (((N : ℂ) ^ (-criticalPoint t) * p) *
          emTailFactor (criticalPoint t) N m).re := by
  rw [eulerMaclaurinApprox_factored hN, add_mul, add_re]
  congr 1
  congr 1
  ring

theorem rotated_em_error_of_prefix_and_last_power {N : ℕ} (hN : 1 ≤ N)
    {t a ea ep : ℝ} {p u : ℂ} {m : ℕ}
    (ha : |(zetaPartialSum (criticalPoint t) N * p).re - a| ≤ ea)
    (hu : ‖(N : ℂ) ^ (-criticalPoint t) * p - u‖ ≤ ep) :
    |(eulerMaclaurinApprox (criticalPoint t) N m * p).re -
      (a + (u * emTailFactor (criticalPoint t) N m).re)| ≤
        ea + ep * ‖emTailFactor (criticalPoint t) N m‖ := by
  have hn := (abs_re_le_norm
    (((N : ℂ) ^ (-criticalPoint t) * p - u) * emTailFactor (criticalPoint t) N m))
  rw [norm_mul] at hn
  have hb := mul_le_mul_of_nonneg_right hu (norm_nonneg (emTailFactor (criticalPoint t) N m))
  have hr : |(((N : ℂ) ^ (-criticalPoint t) * p) *
      emTailFactor (criticalPoint t) N m).re -
        (u * emTailFactor (criticalPoint t) N m).re| ≤
      ep * ‖emTailFactor (criticalPoint t) N m‖ := by
    simpa only [sub_mul, sub_re] using hn.trans hb
  rw [rotated_em_factored hN]
  have ht := abs_add_le ((zetaPartialSum (criticalPoint t) N * p).re - a)
    ((((N : ℂ) ^ (-criticalPoint t) * p) * emTailFactor (criticalPoint t) N m).re -
      (u * emTailFactor (criticalPoint t) N m).re)
  have he : (zetaPartialSum (criticalPoint t) N * p).re +
      (((N : ℂ) ^ (-criticalPoint t) * p) * emTailFactor (criticalPoint t) N m).re -
        (a + (u * emTailFactor (criticalPoint t) N m).re) =
      ((zetaPartialSum (criticalPoint t) N * p).re - a) +
        ((((N : ℂ) ^ (-criticalPoint t) * p) * emTailFactor (criticalPoint t) N m).re -
          (u * emTailFactor (criticalPoint t) N m).re) := by ring
  rw [he]
  exact ht.trans (add_le_add ha hr)

theorem low_positive_of_prefix_and_last_power {t a ea ep δ : ℝ} {p u : ℂ}
    (ht : |t| ≤ 12600) (hp : ‖p - criticalGammaPhase t‖ ≤ δ) (hδ : δ < 1)
    (ha : |(zetaPartialSum (criticalPoint t) (lowPrefix t) * p).re - a| ≤ ea)
    (hu : ‖(lowPrefix t : ℂ) ^ (-criticalPoint t) * p - u‖ ≤ ep)
    (hm : ea + ep * ‖emTailFactor (criticalPoint t) (lowPrefix t) 63‖ +
      ‖p‖ / 1000000000000000000 <
        a + (u * emTailFactor (criticalPoint t) (lowPrefix t) 63).re) :
    0 < normalizedCriticalZeta t :=
  low_positive_of_rotated_em_lower ht hp hδ
    (rotated_em_error_of_prefix_and_last_power (lowPrefix_bounds t).1 ha hu) hm

theorem low_negative_of_prefix_and_last_power {t a ea ep δ : ℝ} {p u : ℂ}
    (ht : |t| ≤ 12600) (hp : ‖p - criticalGammaPhase t‖ ≤ δ) (hδ : δ < 1)
    (ha : |(zetaPartialSum (criticalPoint t) (lowPrefix t) * p).re - a| ≤ ea)
    (hu : ‖(lowPrefix t : ℂ) ^ (-criticalPoint t) * p - u‖ ≤ ep)
    (hm : a + (u * emTailFactor (criticalPoint t) (lowPrefix t) 63).re <
      -(ea + ep * ‖emTailFactor (criticalPoint t) (lowPrefix t) 63‖ +
        ‖p‖ / 1000000000000000000)) :
    normalizedCriticalZeta t < 0 :=
  low_negative_of_rotated_em_upper ht hp hδ
    (rotated_em_error_of_prefix_and_last_power (lowPrefix_bounds t).1 ha hu) hm

#print axioms eulerMaclaurinApprox_factored
#print axioms rotated_em_error_of_prefix_and_last_power
#print axioms low_positive_of_prefix_and_last_power
#print axioms low_negative_of_prefix_and_last_power

end LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate
