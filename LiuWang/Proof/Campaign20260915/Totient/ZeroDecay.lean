import LiuWang.Proof.ChebyshevBound.HighHeight.SmoothedZeroSum

set_option autoImplicit false
noncomputable section

open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.Totient

private theorem zero_exp_height_decay {x u : ℝ}
    (hx : 3100 ≤ Real.log x) (hu : 4 ≤ u)
    (p : RiemannXiDivisorZeroIndex)
    (hp : |(riemannXiDivisorZeroValue p).im| ≤ Real.exp u) :
    Real.exp (((riemannXiDivisorZeroValue p).re - 1) * Real.log x) ≤
      Real.exp (-(Real.log x / (20 * (u + 21 / 10)))) := by
  have hlog : 0 ≤ Real.log (|(riemannXiDivisorZeroValue p).im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg (riemannXiDivisorZeroValue p).im])
  have hheight : Real.log (|(riemannXiDivisorZeroValue p).im| + 2) ≤ u + 1 / 10 :=
    (Real.log_le_log (by positivity) (add_le_add_left hp 2)).trans (log_exp_height_le hu)
  have hi : 1 / (20 * (u + 21 / 10)) ≤
      1 / (20 * (Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 2)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hm := mul_le_mul_of_nonneg_right (hi.trans (xi_zero_gap_twenty p).le)
    (by linarith : 0 ≤ Real.log x)
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm]

theorem xiZeroWeight_sum_le_cutoff {x u : ℝ}
    (hx : 3100 ≤ Real.log x) (hu : 4 ≤ u) :
    (∑' p, xiZeroWeight x p) ≤
      (2 / 3) * Real.exp (-(Real.log x / (20 * (u + 21 / 10)))) +
        (2 * u + 2) / Real.exp u := by
  let E := Real.exp (-(Real.log x / (20 * (u + 21 / 10))))
  have hT : 16 ≤ Real.exp u := by
    have := exp_four_ge_fifty_four.trans (Real.exp_le_exp.mpr hu)
    linarith
  have hpoint (p : RiemannXiDivisorZeroIndex) :
      xiZeroWeight x p ≤ E * (1 / (riemannXiDivisorZeroValue p).im ^ 2) +
        xiHeightTail (Real.exp u) p := by
    by_cases hp : |(riemannXiDivisorZeroValue p).im| ≤ Real.exp u
    · have h := mul_le_mul_of_nonneg_right (zero_exp_height_decay hx hu p hp)
        (by positivity : 0 ≤ 1 / (riemannXiDivisorZeroValue p).im ^ 2)
      have ht := xiHeightTail_nonneg (Real.exp u) p
      dsimp [xiZeroWeight, E] at *
      simpa only [div_eq_mul_inv, mul_one, one_mul] using h.trans (le_add_of_nonneg_right ht)
    · have ht : xiHeightTail (Real.exp u) p =
          1 / (riemannXiDivisorZeroValue p).im ^ 2 :=
        if_pos (lt_of_not_ge hp)
      have h := mul_le_mul_of_nonneg_right (zero_exp_le_one hx p)
        (by positivity : 0 ≤ 1 / (riemannXiDivisorZeroValue p).im ^ 2)
      rw [ht]
      have hE : 0 ≤ E * (1 / (riemannXiDivisorZeroValue p).im ^ 2) := by
        dsimp [E]
        positivity
      simpa only [xiZeroWeight, div_eq_mul_inv, mul_one, one_mul] using
        h.trans (le_add_of_nonneg_left hE)
  have hs := (xiZeroWeight_summable hx).tsum_le_tsum hpoint
    ((xi_height_inverse_square_summable.mul_left E).add
      (xiHeightTail_summable (by linarith : 2 ≤ Real.exp u)))
  rw [Summable.tsum_add (xi_height_inverse_square_summable.mul_left E)
    (xiHeightTail_summable (by linarith : 2 ≤ Real.exp u)), tsum_mul_left] at hs
  have hbase := mul_le_mul_of_nonneg_left xi_height_inverse_square_sum_le
    (Real.exp_pos (-(Real.log x / (20 * (u + 21 / 10))))).le
  have htail := xiHeightTail_sum_le hT
  rw [Real.log_exp] at htail
  dsimp [E] at hs
  nlinarith only [hs, hbase, htail]

private theorem exp_ge_1600_mul_sq {v : ℝ} (hv : 100 ≤ v) :
    1600 * v ^ 2 ≤ Real.exp v := by
  have h6 : v ^ 6 / 720 ≤ Real.exp v := by
    have h := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ v) 7
    have ht : v ^ 6 / (Nat.factorial 6 : ℝ) ≤
        ∑ i ∈ Finset.range 7, v ^ i / (Nat.factorial i : ℝ) :=
      Finset.single_le_sum (f := fun i : ℕ => v ^ i / (Nat.factorial i : ℝ))
        (fun i _ => by positivity) (by norm_num : 6 ∈ Finset.range 7)
    norm_num at ht
    exact ht.trans h
  have h4 : (100 : ℝ) ^ 4 ≤ v ^ 4 := pow_le_pow_left₀ (by norm_num) hv 4
  have hmul := mul_le_mul_of_nonneg_right h4 (sq_nonneg v)
  nlinarith only [h6, hmul, sq_nonneg v]

private theorem exp_sq_ge_linear {v : ℝ} (hv : 100 ≤ v) :
    16 * v + 3 ≤ (Real.exp v) ^ 2 := by
  have he := Real.add_one_le_exp v
  have hv0 : 0 ≤ v := by linarith
  have hsq := sq_le_sq₀ (by linarith : 0 ≤ v + 1) (Real.exp_pos v).le |>.mpr he
  nlinarith

theorem xiZeroWeight_sum_le_log_sixth {x : ℝ}
    (hx : Real.exp 100 ≤ Real.log x) :
    (∑' p, xiZeroWeight x p) ≤ 1 / Real.log x ^ 6 := by
  let L := Real.log x
  let v := Real.log L
  have hL0 : 0 < L := (Real.exp_pos 100).trans_le hx
  have hv : 100 ≤ v := (Real.le_log_iff_exp_le hL0).mpr hx
  have hLv : Real.exp v = L := Real.exp_log hL0
  have hLbig : 3100 ≤ L := by
    have h := exp_ge_1600_mul_sq (by norm_num : (100 : ℝ) ≤ 100)
    norm_num at h
    exact (by linarith : (3100 : ℝ) ≤ Real.exp 100).trans hx
  have hpower : 1600 * v ^ 2 ≤ L := by
    simpa only [hLv] using exp_ge_1600_mul_sq hv
  have hden : 0 < 20 * (8 * v + 21 / 10) := by linarith
  have hquot : 8 * v ≤ L / (20 * (8 * v + 21 / 10)) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hE : Real.exp (-(L / (20 * (8 * v + 21 / 10)))) ≤ 1 / L ^ 8 := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hquot)).trans_eq
    rw [Real.exp_neg, show (8 : ℝ) = (8 : ℕ) by norm_num, Real.exp_nat_mul, hLv]
    simp only [one_div]
  have he8 : Real.exp (8 * v) = L ^ 8 := by
    rw [show (8 : ℝ) = (8 : ℕ) by norm_num, Real.exp_nat_mul, hLv]
  have hs := xiZeroWeight_sum_le_cutoff hLbig (show 4 ≤ 8 * v by linarith)
  change (∑' p, xiZeroWeight x p) ≤
    (2 / 3) * Real.exp (-(L / (20 * (8 * v + 21 / 10)))) +
      (2 * (8 * v) + 2) / Real.exp (8 * v) at hs
  rw [he8] at hs
  have hlin : 16 * v + 3 ≤ L ^ 2 := by
    simpa only [hLv] using exp_sq_ge_linear hv
  calc
    _ ≤ (2 / 3) * (1 / L ^ 8) + (2 * (8 * v) + 2) / L ^ 8 :=
      hs.trans (add_le_add
        (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2 / 3)) le_rfl)
    _ ≤ 1 / L ^ 6 := by
      apply (mul_le_mul_iff_right₀ (pow_pos hL0 8)).mp
      field_simp
      nlinarith only [hlin]

theorem integratedZeroSum_norm_le_log_sixth {x : ℝ} (hx0 : 0 < x)
    (hx : Real.exp 100 ≤ Real.log x) :
    ‖∑' p, integratedZeroTerm x p‖ ≤ x ^ 2 / Real.log x ^ 6 := by
  have h3100 : 3100 ≤ Real.log x := by
    have h := exp_ge_1600_mul_sq (by norm_num : (100 : ℝ) ≤ 100)
    norm_num at h
    linarith
  have h := (integratedZeroTerm_summable hx0 h3100).norm.tsum_le_tsum
    (integratedZeroTerm_norm_le hx0) ((xiZeroWeight_summable h3100).mul_left (x ^ 2))
  rw [tsum_mul_left] at h
  exact (norm_tsum_le_tsum_norm (integratedZeroTerm_summable hx0 h3100).norm).trans
    (h.trans (by simpa only [div_eq_mul_inv, mul_one, one_mul] using
      mul_le_mul_of_nonneg_left (xiZeroWeight_sum_le_log_sixth hx) (sq_nonneg x)))

#print axioms xiZeroWeight_sum_le_cutoff
#print axioms xiZeroWeight_sum_le_log_sixth
#print axioms integratedZeroSum_norm_le_log_sixth

end LiuWang.Proof.Campaign20260915.Totient
