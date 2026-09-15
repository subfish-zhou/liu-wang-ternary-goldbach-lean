import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Expression

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

theorem log_s_ge_three {s : ℝ} (hs : 24 ≤ s) : 3 ≤ Real.log s := by
  apply (Real.le_log_iff_exp_le (by linarith : 0 < s)).mpr
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le
    (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 3
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

theorem logNu_bounds {s : ℝ} (hs : 24 ≤ s) : 2 ≤ logNu s ∧ 0 ≤ logNu s := by
  have hl := log_s_ge_three hs
  have he : 1 ≤ Real.exp Real.eulerMascheroniConstant :=
    Real.one_le_exp_iff.mpr (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  have hp := mul_le_mul_of_nonneg_right he (show 0 ≤ Real.log s by linarith)
  have hd : 0 ≤ 2.50637 / Real.log s := by positivity
  unfold logNu
  constructor <;> nlinarith

theorem logarithm_scaling {s s₀ r : ℝ}
    (hs₀ : 1 ≤ s₀) (hr : 1 ≤ r) (hs : s ≤ s₀ * r) (hspos : 0 < s)
    (hlog : 1 ≤ Real.log s₀) :
    Real.log s ≤ Real.log s₀ * r := by
  have hs₀0 : 0 < s₀ := by linarith
  have hr0 : 0 < r := by linarith
  have h := Real.log_le_log hspos hs
  rw [Real.log_mul hs₀0.ne' hr0.ne'] at h
  have hl := Real.log_le_sub_one_of_pos hr0
  nlinarith

theorem logNu_scaling {s s₀ r : ℝ} (hs₀ : 24 ≤ s₀) (hr : 1 ≤ r)
    (hlo : s₀ ≤ s) (hhi : s ≤ s₀ * r) :
    logNu s ≤ logNu s₀ * r := by
  have hs₀0 : 0 < s₀ := by linarith
  have hs0 : 0 < s := hs₀0.trans_le hlo
  have hlogs := Real.log_le_log hs₀0 hlo
  have hl₀ := log_s_ge_three hs₀
  have hlog := Real.log_le_log hs0 hhi
  rw [Real.log_mul hs₀0.ne' (by linarith : r ≠ 0)] at hlog
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2.50637)
    (by linarith : 0 < Real.log s₀) hlogs
  have hc := mul_le_mul_of_nonneg_left hlog (Real.exp_pos Real.eulerMascheroniConstant).le
  have hrlog : 0 ≤ Real.log r := Real.log_nonneg hr
  have he := mul_le_mul_of_nonneg_right M6Certificate.exp_euler_le_two hrlog
  have hb := (logNu_bounds hs₀).1
  have ht := Real.log_le_sub_one_of_pos (by linarith : 0 < r)
  unfold logNu at hb ⊢
  nlinarith

theorem heightLog_bounds {s : ℝ} (hs : 24 ≤ s) :
    1 ≤ heightLog s ∧ 1 ≤ densityLog s := by
  have hl := Real.log_le_log (by linarith : 0 < s)
    (show s ≤ 10000 * s by linarith)
  dsimp only [densityLog, heightLog]
  constructor <;> linarith [log_s_ge_three hs]

theorem heightLog_scaling {s s₀ r : ℝ} (hs₀ : 24 ≤ s₀) (hr : 1 ≤ r)
    (hlo : s₀ ≤ s) (hhi : s ≤ s₀ * r) :
    heightLog s₀ ≤ heightLog s ∧ heightLog s ≤ heightLog s₀ * r ∧
      densityLog s₀ ≤ densityLog s ∧ densityLog s ≤ densityLog s₀ * r := by
  have hs0 : 0 < s := by linarith
  have hh0 := (heightLog_bounds hs₀).1
  have hlow : heightLog s₀ ≤ heightLog s :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hlo (by norm_num))
  have hhigh : heightLog s ≤ heightLog s₀ * r := by
    apply logarithm_scaling (by linarith : 1 ≤ 10000 * s₀) hr
      (by nlinarith : 10000 * s ≤ (10000 * s₀) * r) (by positivity) hh0
  refine ⟨hlow, hhigh, ?_, ?_⟩ <;> unfold densityLog <;> nlinarith

theorem real_parameter_scaling {L x : ℝ} (hL : 3100 ≤ L)
    (hx : 3 ≤ x) (hx1 : x ≤ 6) :
    24 ≤ x * Real.log 3100 ∧ x * Real.log 3100 ≤ 48.24 ∧
      x * Real.log 3100 ≤ x * Real.log L ∧
      x * Real.log L ≤ (x * Real.log 3100) * (L / 3100) := by
  have hL0 : 0 < L := by linarith
  have hl0 := log_3100_bounds
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 3100) hL
  have hscale := logarithm_scaling (s := L) (s₀ := 3100) (r := L / 3100)
    (by norm_num) (by linarith) (by linarith) hL0 (by linarith [hl0.1])
  refine ⟨by nlinarith [hl0.1], by nlinarith [hl0.2], ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left hlo (by linarith)
  · nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ x by linarith)]

theorem common_exponential_scaling {L x : ℝ} (hL : 3100 ≤ L)
    (hx : 3 ≤ x) (hx1 : x ≤ 6) :
    Real.exp (-0.478 * L / (x * Real.log L + Real.log lowHeight)) ≤
      Real.exp (-0.478 * 3100 / (x * Real.log 3100 + Real.log lowHeight)) /
        (L / 3100) ^ (10 : ℕ) := by
  let z := Real.log (L / 3100)
  let t₀ := x * Real.log 3100 + Real.log lowHeight
  let t := x * Real.log L + Real.log lowHeight
  let A := 0.478 * 3100 / t₀
  have hL0 : 0 < L := by linarith
  have hz : 0 ≤ z := Real.log_nonneg (by linarith)
  have he : Real.exp z = L / 3100 := Real.exp_log (by positivity)
  have ht₀ : 34 ≤ t₀ ∧ t₀ ≤ 59 := by
    have h := real_parameter_scaling hL hx hx1
    dsimp only [t₀]
    constructor <;> linarith [h.1, h.2.1, lowHeight_log_bounds.1, lowHeight_log_bounds.2]
  have ht₀0 : 0 < t₀ := by linarith [ht₀.1]
  have hid : t = t₀ + x * z := by
    dsimp only [t, t₀, z]
    rw [Real.log_div hL0.ne' (by norm_num)]
    ring
  have ht0 : 0 < t := by rw [hid]; nlinarith
  have ht : t ≤ t₀ + 6 * z := by rw [hid]; nlinarith
  have hA : 0 ≤ A := div_nonneg (by norm_num) ht₀0.le
  have hAup : A ≤ 44 := by
    apply (div_le_iff₀ ht₀0).mpr
    linarith [ht₀.1]
  have hAt : A * t₀ = 0.478 * 3100 := div_mul_cancel₀ _ ht₀0.ne'
  have hquad := Real.quadratic_le_exp_of_nonneg hz
  rw [he] at hquad
  have hp := mul_le_mul_of_nonneg_left ht (show 0 ≤ A + 10 * z by positivity)
  have hAz := mul_le_mul_of_nonneg_right hAup hz
  have htz := mul_le_mul_of_nonneg_right ht₀.2 hz
  have hgap : (A + 10 * z) * t ≤ 0.478 * L := by
    nlinarith [sq_nonneg z]
  have hdiv : A + 10 * z ≤ 0.478 * L / t := (le_div_iff₀ ht0).mpr hgap
  calc
    _ ≤ Real.exp (-A - 10 * z) := Real.exp_le_exp.mpr (by
      change -0.478 * L / t ≤ -A - 10 * z
      rw [neg_mul, neg_div]
      linarith)
    _ = _ := by
      rw [Real.exp_sub, show (10 : ℝ) * z = (10 : ℕ) * z by norm_num,
        Real.exp_nat_mul, he]
      congr 1
      congr 1
      dsimp only [A, t₀]
      ring

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
