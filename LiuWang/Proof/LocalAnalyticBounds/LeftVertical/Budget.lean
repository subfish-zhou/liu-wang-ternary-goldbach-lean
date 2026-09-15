import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.Integral

/-! # 原常数 `1.632` 与大 N 支付的纯实数比较 -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical

theorem source_height_log_ge_ninety {T : Real}
    (hT : (2000 : Real) ^ (15 : Nat) ≤ T) : 90 ≤ Real.log T := by
  have he : Real.exp 6 ≤ 2000 := by
    calc
      Real.exp 6 = (Real.exp 1) ^ (6 : Nat) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3 : Real) ^ (6 : Nat) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _
      _ ≤ 2000 := by norm_num
  have hl : 6 ≤ Real.log 2000 := (Real.le_log_iff_exp_le (by norm_num)).mpr he
  have hp := Real.log_le_log (by positivity : (0 : Real) < 2000 ^ (15 : Nat)) hT
  rw [Real.log_pow] at hp
  norm_num at hp
  linarith

theorem normalized_explicit_bound_le_source {q : Nat} (hq : 3 ≤ q) {T : Real}
    (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    (6 * (Real.log q + Real.log (T + 3) + 40) * Real.log (T + 2)) /
      (2 * Real.pi) ≤ 1.632 * Real.log ((q : Real) * T) * Real.log T := by
  have hqpos : (0 : Real) < q := by exact_mod_cast (by omega : 0 < q)
  have hqone : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hTthree : 3 ≤ T := (by norm_num : (3 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  have hTpos : 0 < T := by linarith
  have hlogT := source_height_log_ge_ninety hT
  have hlogq := Real.log_nonneg hqone
  have hQ : 90 ≤ Real.log ((q : Real) * T) := by
    rw [Real.log_mul hqpos.ne' hTpos.ne']
    linarith
  have hshift : ∀ c : Real, 0 ≤ c → c ≤ 3 →
      Real.log (T + c) ≤ Real.log T + 1 := by
    intro c hc hc3
    have hm := Real.log_le_log (by linarith : 0 < T + c)
      (by linarith : T + c ≤ 2 * T)
    rw [Real.log_mul (by norm_num) hTpos.ne'] at hm
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
  have hD : Real.log q + Real.log (T + 3) + 40 ≤
      (3 / 2 : Real) * Real.log ((q : Real) * T) := by
    have hh := hshift 3 (by norm_num) le_rfl
    rw [Real.log_mul hqpos.ne' hTpos.ne'] at *
    linarith
  have hJ : Real.log (T + 2) ≤ (51 / 50 : Real) * Real.log T := by
    have hh := hshift 2 (by norm_num) (by norm_num)
    linarith
  have hJ0 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hQ0 : 0 ≤ Real.log ((q : Real) * T) := by linarith
  have hscale : 0 ≤ Real.log ((q : Real) * T) * Real.log T := by positivity
  apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
  calc
    _ ≤ 6 * ((3 / 2 : Real) * Real.log ((q : Real) * T)) *
        ((51 / 50 : Real) * Real.log T) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hD (by norm_num)) hJ hJ0 (by positivity)
    _ = (459 / 50 : Real) * (Real.log ((q : Real) * T) * Real.log T) := by ring
    _ ≤ (1.632 * (2 * Real.pi)) * (Real.log ((q : Real) * T) * Real.log T) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hscale
    _ = _ := by ring

theorem pow_eighteen_le_exp {x : Real} (hx : 2000 ≤ x) :
    x ^ (18 : Nat) ≤ Real.exp x := by
  have hx0 : 0 ≤ x := by linarith
  have hquad := Real.quadratic_le_exp_of_nonneg (x := x / 18) (by positivity)
  have hsmall : x ≤ Real.exp (x / 18) := by
    nlinarith [mul_nonneg hx0 (show 0 ≤ x - 2000 by linarith)]
  have hp := pow_le_pow_left₀ hx0 hsmall 18
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  rwa [show (18 : Real) * (x / 18) = x by ring] at hp

theorem million_sourceT_le_endpoint {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {t : Real}
    (htlo : sourceWindowLower N ≤ t) :
    1000000 * sourceT N ≤ t := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hc : (1000000000 : Real) ≤ sourceL N ^ (3 : Nat) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2000) hL 3
    norm_num at h
    linarith
  have hNpow : 1000000000 * sourceL N ^ (15 : Nat) ≤ (N : Real) := by
    calc
      _ ≤ sourceL N ^ (3 : Nat) * sourceL N ^ (15 : Nat) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = sourceL N ^ (18 : Nat) := by ring
      _ ≤ Real.exp (sourceL N) := pow_eighteen_le_exp hL
      _ = (N : Real) := exp_sourceL (nat_pos_of_exp_le hN)
  change (N : Real) / 1000 ≤ t at htlo
  change 1000000 * sourceL N ^ (15 : Nat) ≤ t
  linarith

theorem source_left_cost_le_small_budget {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {t : Real}
    (htlo : sourceWindowLower N ≤ t) :
    1.632 * Real.log ((q : Real) * sourceT N) * Real.log (sourceT N) ≤
      (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat) := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hT0 := sourceT_pos hN
  have hqpos : (0 : Real) < q := by exact_mod_cast (by omega : 0 < q)
  have hqone : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hl0 : 0 ≤ Real.log (sourceL N) := Real.log_nonneg (by linarith)
  have hTlog : Real.log (sourceT N) = 15 * Real.log (sourceL N) := log_sourceT N
  have hqlog : Real.log q ≤ 6 * Real.log (sourceL N) := by
    have h := Real.log_le_log hqpos hqUpper
    change Real.log q ≤ Real.log (sourceL N ^ (6 : Nat)) at h
    simpa [Real.log_pow] using h
  have hqT : Real.log ((q : Real) * sourceT N) ≤ 21 * Real.log (sourceL N) := by
    rw [Real.log_mul hqpos.ne' hT0.ne', hTlog]
    linarith
  have hsmall := nat_mul_log_lt (k := 16) hL (by norm_num)
  norm_num only [Nat.cast_ofNat] at hsmall
  have hA : Real.log ((q : Real) * sourceT N) ≤ 2 * sourceL N := by linarith
  have hB : Real.log (sourceT N) ≤ sourceL N := by rw [hTlog]; linarith
  have hB0 : 0 ≤ Real.log (sourceT N) := by rw [hTlog]; positivity
  have hpoly : 1.632 * Real.log ((q : Real) * sourceT N) * Real.log (sourceT N) ≤
      4 * sourceL N ^ (2 : Nat) := by
    calc
      _ ≤ 1.632 * (2 * sourceL N) * sourceL N :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hB hB0 (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (sourceL N)]
  have ht := million_sourceT_le_endpoint hN htlo
  have hr : (4 : Real) ≤ (1 / 100000 : Real) * t / sourceT N := by
    apply (le_div_iff₀ hT0).mpr
    linarith
  exact hpoly.trans (mul_le_mul_of_nonneg_right hr (sq_nonneg _))

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical
