import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityBeta
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.HighEndpointScalar

/-! Theorem 7's displayed density expression at the original height T = L^15. -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

theorem high_endpoint_density_envelope {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sourceDensity q (sourceT N) (59 / 60) ≤ highEndpointDensity (sourceL N) := by
  let L := sourceL N
  let s := Real.log ((q : ℝ) * sourceT N)
  let R := 21 * Real.log L
  let E := L ^ (78 / 60 : ℝ)
  have hL : 3100 ≤ L := sourceL_ge_3100 hN
  have hL0 : 0 < L := by linarith
  have hl : 8 ≤ Real.log L := log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hqlo : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hqlog := Real.log_nonneg hqlo
  have ht : Real.log (sourceT N) = 15 * Real.log L := by
    change Real.log (L ^ 15) = 15 * Real.log L
    rw [Real.log_pow]
    norm_num
  have hqid := Real.log_le_log hqR hq1
  change Real.log q ≤ Real.log (L ^ 6) at hqid
  rw [Real.log_pow] at hqid
  have hs : s = Real.log q + 15 * Real.log L := by
    dsimp only [s]
    rw [Real.log_mul hqR.ne' (by unfold sourceT; positivity), ht]
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hsR : s ≤ R := by dsimp [R]; rw [hs]; norm_num at hqid; linarith
  have hR : 0 < R := by dsimp [R]; linarith
  have hE : 1 ≤ E := Real.one_le_rpow (by linarith) (by norm_num)
  have hD : (q : ℝ) ^ 3 * sourceT N ^ 4 ≤ L ^ (78 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hqR.le hq1 3) (pow_nonneg (show 0 ≤ sourceT N by unfold sourceT; positivity) 4)
    dsimp only [sourceP1, sourceT, L] at h ⊢
    nlinarith only [h]
  have hp : ((q : ℝ) ^ 3 * sourceT N ^ 4) ^ (1 - (59 / 60 : ℝ)) ≤ E := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (q : ℝ) ^ 3 * sourceT N ^ 4)
      hD (by norm_num : 0 ≤ 1 - (59 / 60 : ℝ))
    have hid : (L ^ (78 : ℕ)) ^ (1 - (59 / 60 : ℝ)) = E := by
      rw [← Real.rpow_natCast_mul hL0.le]
      dsimp only [E]
      congr 1
      norm_num
    rwa [hid] at h
  have hsp : s ^ (6 * (59 / 60 : ℝ)) ≤ s ^ (6 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hs1
      (by norm_num : 6 * (59 / 60 : ℝ) ≤ (6 : ℕ))
    simpa only [Real.rpow_natCast] using h
  have hsp6 := pow_le_pow_left₀ (by linarith : 0 ≤ s) hsR 6
  have hsp5 := pow_le_pow_left₀ (by linarith : 0 ≤ s) hsR 5
  have hpoly : (17102 + 254231 / s) * s ^ 6 ≤ (17102 + 254231 / R) * R ^ 6 := by
    have hs0 : s ≠ 0 := by linarith
    have hid (x : ℝ) (hx : x ≠ 0) :
        (17102 + 254231 / x) * x ^ 6 = 17102 * x ^ 6 + 254231 * x ^ 5 := by
      field_simp
    rw [hid s hs0, hid R hR.ne']
    linarith
  have hprin : 16541 * Real.log (sourceT N) ^ 6 ≤ 16541 * R ^ 6 * E := by
    have hpow := pow_le_pow_left₀ (show 0 ≤ Real.log (sourceT N) by rw [ht]; linarith)
      (show Real.log (sourceT N) ≤ R by rw [ht]; dsimp [R]; linarith) 6
    have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ 16541 * R ^ 6 by positivity)
    nlinarith only [hpow, hh]
  have hsec : (17102 + 254231 / s) *
      ((q : ℝ) ^ 3 * sourceT N ^ 4) ^ (1 - (59 / 60 : ℝ)) *
        s ^ (6 * (59 / 60 : ℝ)) ≤ (17102 + 254231 / R) * R ^ 6 * E := by
    have hc : 0 ≤ 17102 + 254231 / s := by positivity
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul hp hsp (Real.rpow_nonneg (by linarith) _) (by positivity)) hc
    have hh := mul_le_mul_of_nonneg_right hpoly (show 0 ≤ E by linarith)
    nlinarith only [h, hh]
  unfold sourceDensity highEndpointDensity
  change 16541 * Real.log (sourceT N) ^ 6 + _ ≤ (33643 + 254231 / R) * R ^ 6 * E
  dsimp only [s] at hsec
  nlinarith only [hprin, hsec]

theorem high_endpoint_source_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ sourceT N := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hqlo : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have ht : sourceL N ^ 2 ≤ sourceT N := by
    exact pow_le_pow_right₀ (by linarith : 1 ≤ sourceL N) (by norm_num : (2 : ℕ) ≤ 15)
  have hl := Real.log_le_sub_one_of_pos hL0
  have hqlog := Real.log_le_log hqR hq1
  rw [sourceP1, Real.log_pow] at hqlog
  have hrat := (div_le_iff₀ hL0).mp (log_over_self_bound hL)
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 100000)
    (by norm_num : (0 : ℝ) < 1) hqlo
  rw [max_le_iff]
  constructor <;> norm_num at hqlog hd <;> nlinarith

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
