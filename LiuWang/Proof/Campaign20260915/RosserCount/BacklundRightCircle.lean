import LiuWang.Proof.Campaign20260915.RosserCount.BacklundEulerMaclaurin
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundEnvelope

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_zeta_right_growth {s : ℂ} (hs : 1 ≤ s.re) (hs' : s.re ≤ 3)
    (ht : 1000 ≤ |s.im|) :
    ‖riemannZeta s‖ < Real.log |s.im| - 0.048 := by
  let t := |s.im|
  let N : ℕ := ⌊t / 3⌋₊ + 1
  have ht0 : 0 < t := by dsimp [t]; linarith
  have ht1000 : 1000 ≤ t := ht
  have hNlo : t / 3 ≤ (N : ℝ) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (t / 3)).le
  have hNhi : (N : ℝ) ≤ t / 3 + 1 := by
    dsimp [N]
    push_cast
    linarith [Nat.floor_le (by positivity : 0 ≤ t / 3)]
  have hN6 : 6 ≤ N := by
    have h : (6 : ℝ) ≤ N := by linarith
    exact_mod_cast h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs1 : s ≠ 1 := by
    intro he
    norm_num [he] at ht
  have hnorm : ‖s‖ ≤ t + 3 := by
    have h := norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at h
    dsimp [t]
    linarith
  have hnorm' : ‖s + 1‖ ≤ t + 4 := by
    have h := norm_le_abs_re_add_abs_im (s + 1)
    simp only [add_re, one_re, add_im, one_im, add_zero] at h
    rw [abs_of_nonneg (by linarith : 0 ≤ s.re + 1)] at h
    dsimp [t]
    linarith
  have hpole : t ≤ ‖s - 1‖ := by
    simpa [t] using abs_im_le_norm (s - 1)
  have hlog : Real.log N ≤ Real.log t - Real.log 3 + 3 / t := by
    have h := Real.log_le_log hN0 hNhi
    have he : t / 3 + 1 = (t / 3) * (1 + 3 / t) := by
      field_simp
    rw [he, Real.log_mul (by positivity) (by positivity),
      Real.log_div ht0.ne' (by norm_num : (3 : ℝ) ≠ 0)] at h
    have hb := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 3 / t)
    linarith
  have hh : 1 / (2 * (N : ℝ)) ≤ 3 / (2 * t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  have hp : 1 / ‖s - 1‖ ≤ 1 / t :=
    one_div_le_one_div_of_le ht0 hpole
  have h1 : ‖s‖ / (12 * (N : ℝ) ^ 2) ≤ 3 * (t + 3) / (4 * t ^ 2) := by
    calc
      _ ≤ (t + 3) / (12 * (t / 3) ^ 2) := by gcongr
      _ = _ := by field_simp; ring
  have h2 :
      ‖s‖ * ‖s + 1‖ / (24 * (N : ℝ) ^ 2) ≤
        3 * (t + 3) * (t + 4) / (8 * t ^ 2) := by
    calc
      _ ≤ (t + 3) * (t + 4) / (24 * (t / 3) ^ 2) := by gcongr
      _ = _ := by field_simp; ring
  have he :
      Real.log t - Real.log 3 + 3 / t + 2 / 3 + 3 / (2 * t) + 1 / t +
          3 * (t + 3) / (4 * t ^ 2) + 3 * (t + 3) * (t + 4) / (8 * t ^ 2) =
        Real.log t + 25 / 24 - Real.log 3 + 71 / (8 * t) + 27 / (4 * t ^ 2) := by
    field_simp
    ring
  have hb :
      ‖riemannZeta s‖ ≤
        Real.log t + 25 / 24 - Real.log 3 + 71 / (8 * t) + 27 / (4 * t ^ 2) := by
    rw [← he]
    linarith [backlund_zeta_em_bound hs hs1 hN6]
  have hc : 71 / (8 * t) ≤ (71 / 8000 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  have hd : 27 / (4 * t ^ 2) ≤ (27 / 4000000 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  change ‖riemannZeta s‖ < Real.log t - 0.048
  linarith [Real.log_three_gt_d9]

private theorem rsA_ge_two_thousand : (2000 : ℝ) ≤ rsA := by
  have h := Real.pow_div_factorial_le_exp (999 / 100 : ℝ) (by norm_num) 8
  norm_num at h
  change (2000 : ℝ) ≤ Real.exp (999 / 100)
  linarith

theorem backlund_right_branch_growth {T u : ℝ} (hT : rsA ≤ T) (hu : |u| = T)
    {s : ℂ} (hs : ‖s‖ ≤ 33 / 25) (hre : 1 ≤ s.re + 5 / 4) :
    ‖riemannZeta (s + 5 / 4 + (u : ℂ) * I)‖ <
      Real.log (T + 33 / 25) - 0.048 := by
  have hTre : 2000 ≤ T := rsA_ge_two_thousand.trans hT
  have hsre := (re_le_norm s).trans hs
  have hsim := (abs_im_le_norm s).trans hs
  have hp : (s + 5 / 4 + (u : ℂ) * I).re = s.re + 5 / 4 := by simp
  have hq : (s + 5 / 4 + (u : ℂ) * I).im = s.im + u := by simp
  have hlo : T - 33 / 25 ≤ |s.im + u| := by
    have h := abs_add_le (s.im + u) (-s.im)
    rw [show s.im + u + -s.im = u by ring, abs_neg, hu] at h
    linarith
  have hhi : |s.im + u| ≤ T + 33 / 25 := by
    have h := abs_add_le s.im u
    rw [hu] at h
    linarith
  have hb := backlund_zeta_right_growth (s := s + 5 / 4 + (u : ℂ) * I)
    (by rw [hp]; exact hre) (by rw [hp]; linarith) (by rw [hq]; linarith)
  rw [hq] at hb
  exact hb.trans_le (sub_le_sub_right
    (Real.log_le_log (by linarith : 0 < |s.im + u|) hhi) _)

theorem backlundCircleEnvelope_right_le {T : ℝ} (hT : rsA ≤ T)
    {s : ℂ} (hs : ‖s‖ ≤ 33 / 25) (hre : 1 ≤ s.re + 5 / 4) :
    backlundCircleEnvelope T s ≤ Real.log (Real.log (T + 33 / 25)) := by
  have hT0 : 0 ≤ T := by linarith [rsA_ge_thousand]
  have hlog : 1 ≤ Real.log (T + 33 / 25) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ T + 33 / 25 by linarith [rsA_ge_thousand])
    linarith [Real.log_three_gt_d9]
  have hnormlog (z : ℂ) (hz : ‖riemannZeta z‖ < Real.log (T + 33 / 25) - 0.048) :
      Real.log ‖riemannZeta z‖ ≤ Real.log (Real.log (T + 33 / 25)) := by
    by_cases hzero : riemannZeta z = 0
    · simpa [hzero] using Real.log_nonneg hlog
    · exact Real.log_le_log (norm_pos_iff.mpr hzero) (by linarith)
  apply max_le
  · exact hnormlog _ (backlund_right_branch_growth hT (abs_of_nonneg hT0) hs hre)
  · have h := backlund_right_branch_growth hT
      (show |(-T)| = T by rw [abs_neg, abs_of_nonneg hT0]) hs hre
    apply hnormlog
    simpa only [ofReal_neg, neg_mul, ← sub_eq_add_neg] using h

#print axioms backlund_zeta_right_growth
#print axioms backlund_right_branch_growth
#print axioms backlundCircleEnvelope_right_le

end LiuWang.Proof.Campaign20260915.RosserCount
