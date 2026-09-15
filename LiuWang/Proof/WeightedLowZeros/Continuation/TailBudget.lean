import LiuWang.Proof.WeightedLowZeros.Continuation.LogBudget

/-! # Numerical tail payments; density and zero-region producers remain separate -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.WeightedLowZeros.Continuation

def cap (N : ℕ) (c : ℝ) : ℝ := 1 - c / Real.log (lowScale N)

theorem decay_with_seed {L c s E : ℝ} (hL : 3100 ≤ L)
    (hc : 0.1 ≤ c) (hs0 : 0 ≤ s) (hs1 : s ≤ 60)
    (hseed : s * 25.33 ≤ 3100 * c) (hE : Real.exp (-s) ≤ E) :
    Real.exp (-c * L / Real.log (3.36 * L^3)) ≤ E * (3100 / L)^5 := by
  let z := Real.log (L / 3100)
  have hp : 0 < L := by linarith
  have hz : 0 ≤ z := Real.log_nonneg (by linarith)
  have he : Real.exp z = L / 3100 := Real.exp_log (by positivity)
  have hquad := Real.quadratic_le_exp_of_nonneg hz
  rw [he] at hquad
  obtain ⟨hlo, hhi⟩ := log_scale_bounds hL
  change Real.log (3.36 * L^3) ≤ 25.33 + 3*z at hhi
  have hprod := mul_le_mul_of_nonneg_left hhi (show 0 ≤ s+5*z by positivity)
  have hcprod := mul_nonneg (show 0 ≤ c-0.1 by linarith) (show 0 ≤ L-3100 by linarith)
  have hsprod := mul_nonneg (show 0 ≤ 60-s by linarith) hz
  have hgap : (s+5*z) * Real.log (3.36 * L^3) ≤ c * L := by
    nlinarith [sq_nonneg z]
  have hquot : s+5*z ≤ c * L / Real.log (3.36 * L^3) :=
    (le_div_iff₀ (by linarith)).mpr hgap
  calc
    _ ≤ Real.exp (-s-5*z) := Real.exp_le_exp.mpr (by rw [neg_mul, neg_div]; linarith)
    _ = Real.exp (-s) * (3100 / L)^5 := by
      have he5 : Real.exp (5*z) = Real.exp z ^5 := by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul z 5
      rw [Real.exp_sub, he5, he]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hE (by positivity)

theorem exp_neg_4038 : Real.exp (-40.38 : ℝ) ≤ 3e-18 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.38) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hs' : (1.46 : ℝ) ≤ Real.exp 0.38 := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 40
  have he : (1 / (3e-18) : ℝ) ≤ Real.exp 40.38 := by
    calc
      _ ≤ (2.7182818283 : ℝ)^40 * 1.46 := by norm_num
      _ ≤ Real.exp 1 ^40 * Real.exp 0.38 :=
        mul_le_mul hp hs' (by norm_num) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / (3e-18)) he
  simpa only [Real.exp_neg, one_div, inv_inv] using h

theorem exp_neg_3942 : Real.exp (-39.42 : ℝ) ≤ 8e-18 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.42) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hs' : (1.52 : ℝ) ≤ Real.exp 0.42 := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 39
  have he : (1 / (8e-18) : ℝ) ≤ Real.exp 39.42 := by
    calc
      _ ≤ (2.7182818283 : ℝ)^39 * 1.52 := by norm_num
      _ ≤ Real.exp 1 ^39 * Real.exp 0.42 :=
        mul_le_mul hp hs' (by norm_num) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / (8e-18)) he
  simpa only [Real.exp_neg, one_div, inv_inv] using h

theorem exp_neg_12687 : Real.exp (-12.687 : ℝ) ≤ 3.1e-6 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.687) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hs' : (1.984 : ℝ) ≤ Real.exp 0.687 := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 12
  have he : (1 / (3.1e-6) : ℝ) ≤ Real.exp 12.687 := by
    calc
      _ ≤ (2.7182818283 : ℝ)^12 * 1.984 := by norm_num
      _ ≤ Real.exp 1 ^12 * Real.exp 0.687 :=
        mul_le_mul hp hs' (by norm_num) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / (3.1e-6)) he
  simpa only [Real.exp_neg, one_div, inv_inv] using h

theorem cap_positive {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {c : ℝ} (hc : c ≤ 0.478) : 0 < cap N c := by
  have hl : 25 ≤ Real.log (lowScale N) := (log_scale_bounds (sourceL_ge_3100 hN)).1
  have hd : c / Real.log (lowScale N) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  dsimp [cap]
  linarith

theorem cap_weight_payment {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {c s E A : ℝ} (hc0 : 0.1 ≤ c) (hc1 : c ≤ 0.478)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 60) (hseed : s * 25.33 ≤ 3100 * c)
    (hE : Real.exp (-s) ≤ E) (hA : 0 ≤ A) (hratio : 1 ≤ A * (1 - c/25)) :
    weight N (cap N c) ≤ (A * E * 3100) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hp : 0 < sourceL N := by linarith
  have hlog : 25 ≤ Real.log (lowScale N) := (log_scale_bounds hL).1
  have hcb : c / Real.log (lowScale N) ≤ c / 25 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hlog
  have hcap : 1-c/25 ≤ cap N c := by dsimp [cap]; linarith
  have hr : (1-(0.001 : ℝ)^cap N c) / cap N c ≤ A := by
    apply (div_le_iff₀ (cap_positive hN hc1)).mpr
    have hm := mul_le_mul_of_nonneg_left hcap hA
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0.001) (cap N c)]
  have hw : weight N (cap N c) ≤ A * Real.exp (-c * sourceL N / Real.log (lowScale N)) := by
    rw [weight_exp_form (nat_pos_of_exp_le hN)]
    have he : (cap N c-1)*sourceL N = -c * sourceL N / Real.log (lowScale N) := by
      unfold cap
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
  have hd := decay_with_seed hL hc0 hs0 hs1 hseed hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le.trans hE
  have ht0 : 0 ≤ 3100 / sourceL N := by positivity
  have ht1 : 3100 / sourceL N ≤ 1 := (div_le_one hp).mpr hL
  have hp5 : (3100 / sourceL N)^5 ≤ 3100 / sourceL N := by
    have h4 : (3100 / sourceL N)^4 ≤ 1 := pow_le_one₀ ht0 ht1
    nlinarith [mul_le_mul_of_nonneg_right h4 ht0,
      show (3100 / sourceL N)^5 = (3100 / sourceL N)^4 * (3100 / sourceL N) by ring]
  calc
    _ ≤ A * (E * (3100 / sourceL N)^5) := hw.trans (mul_le_mul_of_nonneg_left hd hA)
    _ ≤ A * (E * (3100 / sourceL N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp5 hE0) hA
    _ = _ := by ring

theorem weight_033_payment {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weight N (cap N 0.33) ≤ 9.486e-15 / sourceL N := by
  have h := cap_weight_payment hN (c := 0.33) (s := 40.38) (E := 3e-18) (A := 1.02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exp_neg_4038 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem weight_03221_payment {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weight N (cap N 0.3221) ≤ 2.5296e-14 / sourceL N := by
  have h := cap_weight_payment hN (c := 0.3221) (s := 39.42) (E := 8e-18) (A := 1.02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exp_neg_3942 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem weight_source_c1_payment {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weight N (cap N (1/9.645908801)) ≤ 0.00965805 / sourceL N := by
  have h := cap_weight_payment hN (c := 1/9.645908801) (s := 12.687) (E := 3.1e-6) (A := 1.005)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exp_neg_12687 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end LiuWang.Proof.WeightedLowZeros.Continuation
