import LiuWang.Proof.Campaign20260915.Density.PointwiseCritical
import LiuWang.Proof.Campaign20260915.Density.SharpResidueTail

set_option autoImplicit false
noncomputable section

open Finset Complex
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.Campaign20260915.Density

theorem complete_tail_point_energy (q : ℕ) [NeZero q] {X d : ℝ} {s : ℂ}
    (hX : 11 * (q : ℝ) ≤ X) (hd : 0 < d) (hd1 : d ≤ 1) (hs : 1 + d ≤ s.re)
    (S : Finset ℕ) (hS : ∀ n ∈ S, X ≤ (n : ℝ)) :
    (∑ chi : Character q, ‖characterPolynomial chi S
      (fun n => (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s)‖ ^ 2) ≤
      1.1 * X ^ (-2 * d) * (1 + 1 / d) ^ 2 := by
  let a (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s
  let m (x : ZMod q) : ℝ := ∑ n ∈ fiber q S x, ‖a n‖
  let B : ℝ := X ^ (-d) * (1 + 1 / d)
  let C : ℝ := (1.1 / q) * B
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnorm (n : ℕ) (hn : n ∈ S) : ‖a n‖ ≤ (n : ℝ) ^ (-(1 + d)) := by
    have hn1 : (1 : ℝ) ≤ n := hX1.trans (hS n hn)
    have hn0 : n ≠ 0 := by
      have : (0 : ℝ) < n := by linarith
      exact_mod_cast this.ne'
    have h := GlobalZeroDensity.norm_mu_term_le (by linarith : 1 < s.re) n
    rw [LSeries.term_of_ne_zero hn0] at h
    exact h.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hmass (x : ZMod q) : m x ≤ C := by
    exact (sum_le_sum (fun n hn => hnorm n (mem_filter.mp hn).1)).trans
      ((residue_power_tail_sharp x hX hd hd1 hS).trans_eq (by dsimp [C, B]; ring))
  have htotal : (∑ x : ZMod q, m x) ≤ B := by
    dsimp [m]
    rw [sum_all_fibers]
    exact (sum_le_sum hnorm).trans (power_tail_real hX1 hd hS)
  have hsq := sum_le_sum (s := (univ : Finset (ZMod q))) (fun x _ =>
    mul_le_mul_of_nonneg_right (hmass x)
      (show 0 ≤ m x from sum_nonneg (fun _ _ => norm_nonneg _)))
  simp only [← pow_two, ← mul_sum] at hsq
  have hsq' : (∑ x : ZMod q, m x ^ 2) ≤ C * B :=
    hsq.trans (mul_le_mul_of_nonneg_left htotal hC)
  have he : (∑ chi : Character q, ‖characterPolynomial chi S a‖ ^ 2) ≤
      (q.totient : ℝ) * ∑ x : ZMod q, m x ^ 2 := by
    simpa [polynomial, wave, m] using complete_polynomial_point_energy q S a (fun _ => 0) 0
  have hphi : (q.totient : ℝ) ≤ q := Nat.cast_le.mpr (Nat.totient_le q)
  have h := he.trans ((mul_le_mul_of_nonneg_left hsq' (Nat.cast_nonneg q.totient)).trans
    (mul_le_mul_of_nonneg_right hphi (mul_nonneg hC hB)))
  have hc : (q : ℝ) * (C * B) = 1.1 * B ^ 2 := by
    dsimp [C]
    field_simp
  rw [hc] at h
  have hb : B ^ 2 = X ^ (-2 * d) * (1 + 1 / d) ^ 2 := by
    dsimp [B]
    rw [mul_pow, pow_two (X ^ (-d)), ← Real.rpow_add hX0,
      show -d + -d = -2 * d by ring]
  rw [hb] at h
  simpa only [mul_assoc] using h

end LiuWang.Proof.Campaign20260915.Density
