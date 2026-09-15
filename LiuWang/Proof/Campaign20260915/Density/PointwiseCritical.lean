import LiuWang.Proof.Campaign20260915.Density.SievedResidueMass
import LiuWang.Proof.Campaign20260915.Density.OrdinaryCritical

set_option autoImplicit false
noncomputable section

open Finset Complex
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.Campaign20260915.Density

theorem complete_polynomial_point_energy (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (t : ℝ) :
    (∑ chi : Character q, ‖polynomial chi S a w t‖ ^ 2) ≤
      (q.totient : ℝ) * ∑ x : ZMod q, (∑ n ∈ fiber q S x, ‖a n‖) ^ 2 := by
  have he := residue_energy q (residueCoefficient S (fun n => a n * wave (w n) t))
  simp_rw [← characterPolynomial_eq_residuePolynomial] at he
  change (∑ chi : Character q, ‖polynomial chi S a w t‖ ^ 2) = _ at he
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q.totient)
  apply sum_le_sum
  intro x _
  split_ifs
  · apply pow_le_pow_left₀ (norm_nonneg _)
    unfold residueCoefficient
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, norm_wave, mul_one]; rfl)
  · positivity

theorem complete_Q_point_critical (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (t : ℝ) :
    (∑ chi : Character q,
      ‖NonprincipalDensityAdvance.Q chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      2.56 * q.totient * y := by
  simp_rw [Q_critical_eq_wave]
  exact (complete_polynomial_point_energy q _ _ _ t).trans
    ((mul_le_mul_of_nonneg_left (source_residue_critical_mass_sieved q hy)
      (Nat.cast_nonneg q.totient)).trans_eq (by ring))

theorem nonprincipal_Q_point_critical (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (t : ℝ) :
    (∑ chi ∈ nonprincipalCharacters q,
      ‖NonprincipalDensityAdvance.Q chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      2.56 * q.totient * y :=
  (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)).trans
    (complete_Q_point_critical q hy t)

theorem family_point_critical (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (t : ℝ) :
    (∑ chi ∈ nonprincipalCharacters q,
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      41.00096 * (q : ℝ) * Real.sqrt q * y * Real.log q * (2 + |t|) + 1001 * q := by
  let C : ℝ := 16.016 * ((q : ℝ) * Real.sqrt q * Real.log q / q.totient) * (2 + |t|)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (chi : Character q) (hc : chi ∈ nonprincipalCharacters q) :
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤
        C * ‖NonprincipalDensityAdvance.Q chi ((q : ℝ) * y)
          ((1 / 2 : ℂ) + t * I)‖ ^ 2 + 1001 := by
    have hL := mul_le_mul_of_nonneg_right
      (ordinary_critical_L_sq ((mem_nonprincipalCharacters chi).mp hc) (le_refl |t|))
      (sq_nonneg ‖NonprincipalDensityAdvance.Q chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * I)‖)
    dsimp [C]
    nlinarith only [hL, detector_small_young chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * I)]
  have h := sum_le_sum hpoint
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at h
  have hc : ((nonprincipalCharacters q).card : ℝ) ≤ q := by
    rw [card_nonprincipalCharacters]
    exact_mod_cast (Nat.sub_le q.totient 1).trans (Nat.totient_le q)
  have hm := mul_le_mul_of_nonneg_left (nonprincipal_Q_point_critical q hy t) hC
  have he : C * (2.56 * q.totient * y) =
      41.00096 * (q : ℝ) * Real.sqrt q * y * Real.log q * (2 + |t|) := by
    dsimp [C]
    field_simp
    ring
  rw [he] at hm
  linarith only [h, hm, hc]

end LiuWang.Proof.Campaign20260915.Density
