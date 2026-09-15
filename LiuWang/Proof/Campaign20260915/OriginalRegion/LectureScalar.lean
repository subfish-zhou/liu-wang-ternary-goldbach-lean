import LiuWang.Proof.Campaign20260915.OriginalRegion.HigherOrderBudget

/-! Exact radical arithmetic for the original c1, without numerical sampling. -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem lecture_original_scalar :
    36.506331844352 * stechkinConductorCoeff <
      9.645908801 * (Real.sqrt 19.073344004352 - Real.sqrt 11.1859355312082048) ^ 2 := by
  let a : ℝ := 11.1859355312082048
  let b : ℝ := 19.073344004352
  let c : ℝ := 36.506331844352 / (2 * 9.645908801)
  let x : ℝ := a + b - c
  let d : ℝ := 4 * a * b - x ^ 2 - c ^ 2 / 5
  have ha : 0 < a := by norm_num [a]
  have hb : 0 < b := by norm_num [b]
  have hc : 0 < c := by norm_num [c]
  have hx : 0 < x := by norm_num [x, a, b, c]
  have hd : 0 < d := by norm_num [d, x, a, b, c]
  have hsep : 5 * d ^ 2 < 4 * x ^ 2 * c ^ 2 := by norm_num [d, x, a, b, c]
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hu : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by positivity)
  have hu0 : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hdsep : d * Real.sqrt 5 < 2 * x * c := by
    have hh : (d * Real.sqrt 5) ^ 2 < (2 * x * c) ^ 2 := by
      rw [mul_pow, hs]
      nlinarith only [hsep]
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hh
  have he : (Real.sqrt (a * b) * Real.sqrt 5) ^ 2 = 5 * a * b := by
    rw [mul_pow, hu, hs]
    ring
  have hdid : 5 * d = 20 * a * b - 5 * x ^ 2 - c ^ 2 := by dsimp [d]; ring
  have hm := mul_lt_mul_of_pos_right hdsep hs0
  have hrad : 2 * (Real.sqrt (a * b) * Real.sqrt 5) < x * Real.sqrt 5 + c := by
    have hpos : 0 < x * Real.sqrt 5 + c := by positivity
    nlinarith [sq_nonneg (x * Real.sqrt 5 + c - 2 * (Real.sqrt (a * b) * Real.sqrt 5))]
  have hbound : 2 * Real.sqrt (a * b) < x + c / Real.sqrt 5 := by
    have hh : (2 * Real.sqrt (a * b)) * Real.sqrt 5 < x * Real.sqrt 5 + c := by
      nlinarith only [hrad]
    calc
      2 * Real.sqrt (a * b) < (x * Real.sqrt 5 + c) / Real.sqrt 5 :=
        (lt_div_iff₀ hs0).mpr hh
      _ = x + c / Real.sqrt 5 := by
        rw [add_div, mul_div_cancel_right₀ _ hs0.ne']
  have hmul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha.le b
  have hsa := Real.sq_sqrt ha.le
  have hsb := Real.sq_sqrt hb.le
  rw [hmul] at hbound
  dsimp [x, c, a, b] at hbound hsa hsb
  dsimp [stechkinConductorCoeff, stechkinK]
  simp only [div_eq_mul_inv] at hbound ⊢
  nlinarith only [hbound, hsa, hsb]

def lectureShift : ℝ :=
  Real.sqrt 11.1859355312082048 /
    (9.645908801 * (Real.sqrt 19.073344004352 - Real.sqrt 11.1859355312082048))

theorem lectureShift_properties :
    0 < lectureShift ∧ lectureShift ≤ 17 / 50 ∧
      (11.1859355312082048 / lectureShift + 36.506331844352 * stechkinConductorCoeff) *
        (lectureShift + 1 / 9.645908801) < 19.073344004352 := by
  let r := Real.sqrt 11.1859355312082048
  let s := Real.sqrt 19.073344004352
  have hr : r ^ 2 = 11.1859355312082048 := Real.sq_sqrt (by norm_num)
  have hs : s ^ 2 = 19.073344004352 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hrs : r < s := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hdiff : 0 < s - r := sub_pos.mpr hrs
  have hA : 0 < lectureShift := by change 0 < r / (9.645908801 * (s - r)); positivity
  have hAeq : lectureShift * (9.645908801 * (s - r)) = r := by
    exact div_mul_cancel₀ r (by positivity)
  have hsq : ((1 + (17 / 50 : ℝ) * 9.645908801) * r) ^ 2 ≤
      ((17 / 50 : ℝ) * 9.645908801 * s) ^ 2 := by nlinarith only [hr, hs]
  have hle := (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have hAmax : lectureShift ≤ 17 / 50 := by nlinarith only [hAeq, hle, hdiff]
  refine ⟨hA, hAmax, ?_⟩
  have hcert := lecture_original_scalar
  change 36.506331844352 * stechkinConductorCoeff < 9.645908801 * (s - r) ^ 2 at hcert
  have hid :
      (r ^ 2 / lectureShift + 36.506331844352 * stechkinConductorCoeff) *
        (lectureShift + 1 / 9.645908801) =
      s ^ 2 + (36.506331844352 * stechkinConductorCoeff -
        9.645908801 * (s - r) ^ 2) * (lectureShift + 1 / 9.645908801) := by
    change (r ^ 2 / (r / (9.645908801 * (s - r))) +
      36.506331844352 * stechkinConductorCoeff) *
        (r / (9.645908801 * (s - r)) + 1 / 9.645908801) = _
    change _ = s ^ 2 + (36.506331844352 * stechkinConductorCoeff -
      9.645908801 * (s - r) ^ 2) *
        (r / (9.645908801 * (s - r)) + 1 / 9.645908801)
    field_simp
    ring
  rw [hr, hs] at hid
  have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr hcert)
    (show 0 < lectureShift + 1 / 9.645908801 by positivity)
  linarith

theorem lecture_scaled_budget_contradiction {L beta : ℝ} (hL : 0 < L)
    (hb : beta < 1) (hgap : (1 - beta) * L ≤ 1 / 9.645908801)
    (hbudget : 19.073344004352 / (1 + lectureShift / L - beta) ≤
      11.1859355312082048 / (lectureShift / L) +
        36.506331844352 * stechkinConductorCoeff * L) : False := by
  obtain ⟨hA, _, hcert⟩ := lectureShift_properties
  let d := (1 - beta) * L
  have hd : 0 < d := mul_pos (sub_pos.mpr hb) hL
  have hden : 1 + lectureShift / L - beta = (lectureShift + d) / L := by
    dsimp [d]
    field_simp
    ring
  rw [hden] at hbudget
  have hid1 : 19.073344004352 / ((lectureShift + d) / L) =
      (19.073344004352 / (lectureShift + d)) * L := by field_simp
  have hid2 : 11.1859355312082048 / (lectureShift / L) =
      (11.1859355312082048 / lectureShift) * L := by field_simp
  rw [hid1, hid2] at hbudget
  have hscaled : 19.073344004352 / (lectureShift + d) ≤
      11.1859355312082048 / lectureShift + 36.506331844352 * stechkinConductorCoeff :=
    (mul_le_mul_iff_left₀ hL).mp (by nlinarith only [hbudget])
  have hmul := (div_le_iff₀ (show 0 < lectureShift + d by positivity)).mp hscaled
  have hCpos : 0 < 11.1859355312082048 / lectureShift +
      36.506331844352 * stechkinConductorCoeff := by
    have hk := conductorCoeff_bounds.1
    positivity
  have hstrict := mul_le_mul_of_nonneg_left (add_le_add_left hgap lectureShift) hCpos.le
  linarith

theorem originalGap_le_lectureShift : 1 / 9.645908801 ≤ lectureShift := by
  have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11.1859355312082048)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19.073344004352)
  have hr0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 11.1859355312082048)
  have hs0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 19.073344004352)
  have hrs := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 11.1859355312082048)
    (by norm_num : (11.1859355312082048 : ℝ) < 19.073344004352)
  unfold lectureShift
  apply (le_div_iff₀ (by positivity)).mpr
  simp only [div_eq_mul_inv]
  nlinarith [sq_nonneg (2 * Real.sqrt 11.1859355312082048 - Real.sqrt 19.073344004352)]

end LiuWang.Proof.Campaign20260915.OriginalRegion
