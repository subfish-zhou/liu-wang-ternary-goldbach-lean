import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27.Difference
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Kernel

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27

namespace LiuWang.Proof.Campaign20260915.HighSums

theorem short_main_nonneg {s : ℝ} (hs : 10 ≤ s) :
    0 ≤ s / Real.pi - 0.874 := by
  have h : 0.874 ≤ s / Real.pi :=
    (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
  linarith

theorem differenceKernel_le_positive_correction (L : ℝ) (q : ℕ) [NeZero q]
    {s : ℝ} (hs : 10 ≤ s) :
    differenceKernel L q q.totient s ≤
      L ^ 4 * q.totient * (6.8423 * s + 15) *
        Real.exp (-s) * Real.exp (-0.478 * L / s) := by
  have hA := short_main_nonneg hs
  have hB : 0 ≤ 6.8423 * s + 15 := by linarith
  have hlast : 0 ≤ L ^ 4 *
      ((q.totient : ℝ) / q * (s / Real.pi - 0.874) +
        q.totient * (6.8423 * s + 15) * Real.exp (-s)) * Real.exp (-L / 20) := by
    positivity
  have hmain := main_coefficient_difference_nonpos q hs
  have hcoeff :
      ((q.totient : ℝ) / q - 1) * (s / Real.pi - 0.874) +
        (q.totient - 1 / 700000) * (6.8423 * s + 15) * Real.exp (-s) ≤
      q.totient * (6.8423 * s + 15) * Real.exp (-s) := by
    calc
      _ ≤ (q.totient - 1 / 700000 : ℝ) * (6.8423 * s + 15) * Real.exp (-s) :=
        add_le_of_nonpos_left hmain
      _ ≤ _ := by gcongr; norm_num
  unfold differenceKernel
  exact (sub_le_self _ hlast).trans
    ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoeff (by positivity)) (Real.exp_pos _).le).trans_eq
      (by ring))

theorem combined_exponent_mono {k s b : ℝ} (hs : 0 < s) (hsb : s ≤ b)
    (hbk : b ^ 2 ≤ k) :
    -s - k / s ≤ -b - k / b := by
  have hb : 0 < b := hs.trans_le hsb
  have hbs : b * s ≤ k := by nlinarith
  have hh := mul_nonneg (sub_nonneg.mpr hsb) (sub_nonneg.mpr hbs)
  apply (mul_le_mul_iff_right₀ (mul_pos hs hb)).mp
  field_simp
  nlinarith

theorem transferRemainder_le_endpoint {L t b : ℝ} (hL : 3100 ≤ L)
    (q : ℕ) [NeZero q] (hq : (q : ℝ) ≤ L ^ 3)
    (ht : lower L ≤ t) (htu : t ≤ upper L) (hb : upper L ≤ b)
    (hbk : b ^ 2 ≤ 0.478 * L) :
    transferRemainder L q q.totient t ≤
      b * L ^ 7 * (6.8423 * b + 15) * Real.exp (-b - 0.478 * L / b) := by
  have ha := (original_endpoints hL).1
  have htb := htu.trans hb
  have hb0 : 0 < b := by linarith
  have hL0 : 0 < L := by linarith
  let C : ℝ := L ^ 7 * (6.8423 * b + 15) * Real.exp (-b - 0.478 * L / b)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hphi : (q.totient : ℝ) ≤ L ^ 3 :=
    (Nat.cast_le.mpr (Nat.totient_le q)).trans hq
  have hm : (∫ s in lower L..t, differenceKernel L q q.totient s) ≤
      (t - lower L) * C := by
    have hh := intervalIntegral.integral_mono_on ht
      (differenceKernel_integrable L q q.totient ha ht)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume (lower L) t)
      (fun s hs => by
        have hs10 : 10 ≤ s := ha.trans hs.1
        have hs0 : 0 < s := by linarith
        have hsb := hs.2.trans htb
        have he := Real.exp_le_exp.mpr (combined_exponent_mono hs0 hsb hbk)
        have hB : 0 ≤ 6.8423 * s + 15 := by linarith
        apply (differenceKernel_le_positive_correction L q hs10).trans
        rw [mul_assoc _ (Real.exp (-s)), ← Real.exp_add]
        rw [show -s + -0.478 * L / s = -s - 0.478 * L / s by ring]
        have hc : L ^ 4 * q.totient * (6.8423 * s + 15) ≤
            L ^ 7 * (6.8423 * b + 15) := by
          calc
            _ ≤ L ^ 4 * L ^ 3 * (6.8423 * b + 15) := by gcongr
            _ = _ := by ring
        exact mul_le_mul hc he (Real.exp_pos _).le (by positivity))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
  have htail : 0 ≤ ∫ s in t..upper L, integrand L s := by
    apply intervalIntegral.integral_nonneg htu
    intro s hs
    have hs10 : 10 ≤ s := (ha.trans ht).trans hs.1
    have hA := short_main_nonneg hs10
    have hB : 0 ≤ 6.8423 * s + 15 := by linarith
    rw [integrand_grouped]
    positivity
  have hlength : t - lower L ≤ b := by linarith
  unfold transferRemainder
  exact ((sub_le_self _ htail).trans hm).trans
    ((mul_le_mul_of_nonneg_right hlength hC).trans_eq (by dsimp only [C]; ring))

theorem short_correction_endpoint_certificate :
    (36.511 : ℝ) * 3100 ^ 7 * (6.8423 * 36.511 + 15) * Real.exp (-77) ≤
      4 / 100000 := by
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
    ((by norm_num : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le) 77
  rw [← Real.exp_nat_mul] at he
  simp only [Nat.cast_ofNat, mul_one] at he
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos 77)).mpr
  exact (by norm_num :
    (36.511 : ℝ) * 3100 ^ 7 * (6.8423 * 36.511 + 15) ≤
      (4 / 100000 : ℝ) * (27 / 10) ^ 77).trans
    (mul_le_mul_of_nonneg_left he (by norm_num))

theorem short_correction_scaled {u : ℝ} (hu : 1 ≤ u) :
    (36.511 * u) * (3100 * u ^ 8) ^ 7 * (6.8423 * (36.511 * u) + 15) *
      Real.exp (-(36.511 * u) - 0.478 * (3100 * u ^ 8) / (36.511 * u)) ≤
        4 / 100000 := by
  have hu0 : 0 < u := by linarith
  have hp : u ≤ u ^ 7 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hu (by norm_num : 1 ≤ 7))
  have heq : -(36.511 * u) - 0.478 * (3100 * u ^ 8) / (36.511 * u) =
      -36.511 * u - (0.478 * 3100 / 36.511) * u ^ 7 := by
    field_simp
  have hex : Real.exp (-(36.511 * u) - 0.478 * (3100 * u ^ 8) / (36.511 * u)) ≤
      Real.exp (-77 * u) := by
    apply Real.exp_le_exp.mpr
    rw [heq]
    nlinarith
  have hpoly :
      (36.511 * u) * (3100 * u ^ 8) ^ 7 * (6.8423 * (36.511 * u) + 15) ≤
      (36.511 * 3100 ^ 7 * (6.8423 * 36.511 + 15)) * u ^ 58 := by
    calc
      _ ≤ (36.511 * u) * (3100 * u ^ 8) ^ 7 *
          ((6.8423 * 36.511 + 15) * u) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ = _ := by ring
  have hh := mul_le_mul hpoly hex (Real.exp_pos _).le (by positivity)
  have hd := Source26Certificate.power_exp_le (c := 77) 58
    (by norm_num : (0 : ℝ) < 1) hu (by norm_num)
  norm_num only [one_pow, mul_one, one_mul] at hd
  have hf := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ (36.511 : ℝ) * 3100 ^ 7 * (6.8423 * 36.511 + 15) by positivity)
  have hf' :
      (36.511 * 3100 ^ 7 * (6.8423 * 36.511 + 15)) * u ^ 58 * Real.exp (-77 * u) ≤
      (36.511 * 3100 ^ 7 * (6.8423 * 36.511 + 15)) * Real.exp (-77) := by
    simpa only [mul_assoc] using hf
  exact hh.trans (hf'.trans short_correction_endpoint_certificate)

theorem transferRemainder_le_four_div_hundred_thousand {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hshort : omegaCutoff N q < q1 q) :
    transferRemainder (sourceL N) q q.totient (Real.log ((q : ℝ) * q1 q)) ≤
      4 / 100000 := by
  let L := sourceL N
  let u : ℝ := (L / 3100) ^ (1 / 8 : ℝ)
  have hL : 3100 ≤ L := Parameters.sourceL_ge_3100 hN
  have hu : 1 ≤ u := Real.one_le_rpow (by linarith : 1 ≤ L / 3100) (by norm_num)
  have hu8 : u ^ 8 = L / 3100 := by
    dsimp only [u]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ L / 3100)]
    norm_num
  have he : L = 3100 * u ^ 8 := by rw [hu8]; ring
  have hb : upper L ≤ 36.511 * u := by
    rw [he]
    exact source27_scaled_log_endpoint hu
  have hp : u ^ 2 ≤ u ^ 8 := pow_le_pow_right₀ hu (by norm_num)
  have hbk : (36.511 * u) ^ 2 ≤ 0.478 * L := by
    rw [he]
    nlinarith [sq_nonneg u]
  have hd := short_domain hN hq hshort
  have hh := transferRemainder_le_endpoint hL q hq hd.2.2.2.1 hd.2.2.2.2 hb hbk
  rw [he] at hh
  simpa only [← he] using hh.trans (short_correction_scaled hu)

#print axioms differenceKernel_le_positive_correction
#print axioms transferRemainder_le_four_div_hundred_thousand

end LiuWang.Proof.Campaign20260915.HighSums
