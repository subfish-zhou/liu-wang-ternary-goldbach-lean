import LiuWang.Proof.Campaign20260915.Totient.ThetaPrefix

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.Totient

private theorem block_zero : thetaWalk 0 200 (prefixUnits thetaLogRows 0) := by decide +kernel
private theorem block_two : thetaWalk 200 200 (prefixUnits thetaLogRows 200) := by decide +kernel
private theorem block_four : thetaWalk 400 200 (prefixUnits thetaLogRows 400) := by decide +kernel
private theorem block_six : thetaWalk 600 200 (prefixUnits thetaLogRows 600) := by decide +kernel
private theorem block_eight : thetaWalk 800 200 (prefixUnits thetaLogRows 800) := by decide +kernel
private theorem block_ten : thetaWalk 1000 200 (prefixUnits thetaLogRows 1000) := by decide +kernel
private theorem block_twelve : thetaWalk 1200 100 (prefixUnits thetaLogRows 1200) := by decide +kernel

theorem theta_table_certificate {n : ℕ} (hn : n ≤ 1420) :
    (((min (n + 1) 1420 : ℕ) : ℤ) * 10000000000 - thetaInteger n) ^ 2 <
      4 * (min (n + 1) 1420 : ℕ) * 10000000000 ^ 2 := by
  have useBlock {a k : ℕ} (h : thetaWalk a k (prefixUnits thetaLogRows a))
      (ha : a ≤ n) (hk : n < a + k) := thetaWalk_sound
        (by simpa only [thetaInteger_eq_prefixUnits] using h) n ha hk
  by_cases h0 : n < 200
  · exact useBlock block_zero (by omega) h0
  by_cases h2 : n < 400
  · exact useBlock block_two (by omega) (by omega)
  by_cases h4 : n < 600
  · exact useBlock block_four (by omega) (by omega)
  by_cases h6 : n < 800
  · exact useBlock block_six (by omega) (by omega)
  by_cases h8 : n < 1000
  · exact useBlock block_eight (by omega) (by omega)
  by_cases h10 : n < 1200
  · exact useBlock block_ten (by omega) (by omega)
  by_cases h12 : n < 1300
  · exact useBlock block_twelve (by omega) (by omega)
  exact theta_integer_tail (by omega) hn

noncomputable section

theorem theta_gt_sub_two_sqrt_upto_1420 {x : ℝ} (hx : 0 < x) (h1420 : x ≤ 1420) :
    x - 2 * Real.sqrt x < Chebyshev.theta x := by
  by_cases h1 : x ≤ 1
  · have hs := Real.sq_sqrt hx.le
    have hp := Real.sqrt_pos.mpr hx
    have hle : x ≤ Real.sqrt x := by nlinarith [Real.sqrt_nonneg x]
    exact (by linarith : x - 2 * Real.sqrt x < 0).trans_le
      (Chebyshev.theta_nonneg x)
  have hn : ⌊x⌋₊ ≤ 1420 := by
    exact (Nat.floor_le_floor h1420).trans_eq (by norm_num)
  let b : ℕ := min (⌊x⌋₊ + 1) 1420
  let t : ℝ := (thetaInteger ⌊x⌋₊ : ℝ) / 10000000000
  have ht := theta_table_certificate hn
  have htr0 : ((b : ℝ) * 10000000000 - thetaInteger ⌊x⌋₊) ^ 2 <
      4 * (b : ℝ) * 10000000000 ^ 2 := by
    exact_mod_cast ht
  have htr : ((b : ℝ) - t) ^ 2 < 4 * b := by
    dsimp [t]
    nlinarith
  have hb : x ≤ (b : ℝ) := by
    simp only [b, Nat.cast_min, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    exact le_min (Nat.lt_floor_add_one x).le h1420
  have hsx := Real.sq_sqrt hx.le
  have hsb := Real.sq_sqrt (show (0 : ℝ) ≤ b by positivity)
  have hsm := Real.sqrt_le_sqrt hb
  have hsl : 1 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ x by linarith)
    simpa using h
  have hmain : (b : ℝ) - 2 * Real.sqrt b < t := by
    nlinarith [sq_nonneg ((b : ℝ) - t + 2 * Real.sqrt b)]
  have hmono : x - 2 * Real.sqrt x ≤
      (b : ℝ) - 2 * Real.sqrt b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsm)
      (show 0 ≤ Real.sqrt x + Real.sqrt b - 2 by linarith)]
  exact (hmono.trans_lt hmain).trans_le
    ((thetaInteger_le_theta ⌊x⌋₊).trans
      (Chebyshev.theta_mono (Nat.floor_le hx.le)))

theorem lemma15_middle_theta {L : ℝ} (h255 : 255 ≤ L) (h1340 : L ≤ 1340) :
    L < Chebyshev.theta (L + (2 + 2 * Real.sqrt (1 + L))) := by
  let x := L + (2 + 2 * Real.sqrt (1 + L))
  have hs := Real.sq_sqrt (show 0 ≤ 1 + L by linarith)
  have hr : Real.sqrt (1 + L) < 39 := by
    nlinarith [Real.sqrt_nonneg (1 + L)]
  have hx0 : 0 < x := by dsimp [x]; nlinarith [Real.sqrt_nonneg (1 + L)]
  have hxhi : x ≤ 1420 := by dsimp [x]; linarith
  have hroot : Real.sqrt x = 1 + Real.sqrt (1 + L) := by
    have he : x = (1 + Real.sqrt (1 + L)) ^ 2 := by dsimp [x]; nlinarith
    rw [he, Real.sqrt_sq (by positivity)]
  have ht := theta_gt_sub_two_sqrt_upto_1420 hx0 hxhi
  rw [hroot] at ht
  dsimp [x] at *
  linarith

#print axioms theta_table_certificate
#print axioms theta_gt_sub_two_sqrt_upto_1420
#print axioms lemma15_middle_theta

end
end LiuWang.Proof.Campaign20260915.Totient
