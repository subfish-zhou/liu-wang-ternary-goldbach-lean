import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.PhaseScaling

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart

def lowerLog (L : ℝ) : ℝ := Real.log (3.36 * L ^ (3 : ℕ))
def upperLog (L : ℝ) : ℝ := Real.log (10 * Real.pi * L ^ (7 : ℕ))

theorem base_log_domain :
    20 ≤ lowerLog 3100 ∧ upperLog 3100 ≤ 60 ∧ 4 ≤ upperLog 3100 - lowerLog 3100 := by
  have hl := log_3100_bounds
  have hlo : 0 ≤ Real.log (3.36 : ℝ) := Real.log_nonneg (by norm_num)
  have hup : Real.log (3.36 : ℝ) ≤ 3 :=
    (Real.log_le_sub_one_of_pos (by norm_num : 0 < (3.36 : ℝ))).trans (by norm_num)
  have hpi : 0 ≤ Real.log (10 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  unfold lowerLog upperLog
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by positivity) (by norm_num)]
  simp only [Real.log_pow, Nat.cast_ofNat]
  exact ⟨by linarith, by linarith [log_ten_pi_le_35], by linarith⟩

theorem source_log_scaling {L : ℝ} (hL : 3100 ≤ L) :
    lowerLog L = lowerLog 3100 + 3 * Real.log (L / 3100) ∧
      upperLog L = upperLog 3100 + 7 * Real.log (L / 3100) := by
  have hLp : 0 < L := by linarith
  have hl : Real.log L = Real.log (3100 : ℝ) + Real.log (L / 3100) := by
    rw [Real.log_div hLp.ne' (by norm_num)]
    ring
  unfold lowerLog upperLog
  simp only [Real.log_mul (by norm_num : (3.36 : ℝ) ≠ 0) (by positivity : L ^ (3 : ℕ) ≠ 0),
    Real.log_mul (by norm_num : (3.36 : ℝ) ≠ 0) (by norm_num : (3100 : ℝ) ^ (3 : ℕ) ≠ 0),
    Real.log_mul (by positivity : 10 * Real.pi ≠ 0) (by positivity : L ^ (7 : ℕ) ≠ 0),
    Real.log_mul (by positivity : 10 * Real.pi ≠ 0) (by norm_num : (3100 : ℝ) ^ (7 : ℕ) ≠ 0),
    Real.log_pow, Nat.cast_ofNat]
  rw [hl]
  constructor <;> ring

theorem window_H_scaling {L : ℝ} (hL : 3100 ≤ L) :
    3093 ≤ (3100 : ℝ) + Real.log 0.001 ∧
      ((3100 : ℝ) + Real.log 0.001) * (L / 3100) ≤ L + Real.log 0.001 := by
  have h := original_H_ge_scaling (L := (3100 : ℝ)) (by norm_num)
  have hs : scaling (3100 : ℝ) = 1 := by norm_num [scaling]
  rw [hs] at h
  norm_num only [one_pow, mul_one] at h
  have ht : 1 ≤ L / 3100 := by linarith
  have hc : Real.log (0.001 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hm := mul_nonneg (neg_nonneg.mpr hc) (sub_nonneg.mpr ht)
  refine ⟨?_, by nlinarith only [hm]⟩
  convert h using 1
  norm_num

theorem sourceNu_linear_scaling {L : ℝ} (hL : 3100 ≤ L) :
    0 ≤ sourceNu ((3100 : ℝ) ^ (3 : ℕ)) ∧
      sourceNu (L ^ (3 : ℕ)) ≤ (L / 3100) * sourceNu ((3100 : ℝ) ^ (3 : ℕ)) := by
  let t := L / 3100
  let b := Real.log (Real.log ((3100 : ℝ) ^ (3 : ℕ)))
  let c := Real.log (Real.log (L ^ (3 : ℕ)))
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := by linarith
  have hb : 3 ≤ b := (source_loglog_bounds (L := (3100 : ℝ)) (by norm_num)).1
  have hbc : b ≤ c := by
    apply Real.log_le_log
    · rw [Real.log_pow]
      have hh := log_3100_bounds.1
      norm_num only [Nat.cast_ofNat]
      linarith
    · apply Real.log_le_log (by norm_num)
      exact pow_le_pow_left₀ (by norm_num) hL _
  have hbase : Real.log (L ^ (3 : ℕ)) =
      Real.log ((3100 : ℝ) ^ (3 : ℕ)) + 3 * Real.log t := by
    have hl : Real.log L = Real.log (3100 : ℝ) + Real.log t := by
      dsimp [t]
      rw [Real.log_div (by positivity) (by norm_num)]
      ring
    simp only [Real.log_pow, Nat.cast_ofNat, hl]
    ring
  have hb1 : 1 ≤ Real.log ((3100 : ℝ) ^ (3 : ℕ)) := by
    rw [Real.log_pow]
    have hh := log_3100_bounds.1
    norm_num only [Nat.cast_ofNat]
    linarith
  have hlogs : Real.log (L ^ (3 : ℕ)) ≤ t * Real.log ((3100 : ℝ) ^ (3 : ℕ)) := by
    rw [hbase]
    have h7 : 3 ≤ Real.log ((3100 : ℝ) ^ (3 : ℕ)) := by
      rw [Real.log_pow]
      have hh := log_3100_bounds.1
      norm_num only [Nat.cast_ofNat]
      linarith
    nlinarith [Real.log_le_sub_one_of_pos ht0,
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr h7)]
  have hclog : c ≤ b + Real.log t := by
    have hp : 0 < Real.log (L ^ (3 : ℕ)) := by
      rw [hbase]
      exact add_pos_of_pos_of_nonneg (by linarith)
        (mul_nonneg (by norm_num) (Real.log_nonneg ht))
    have hh := Real.log_le_log hp hlogs
    rw [Real.log_mul ht0.ne' (by linarith : Real.log ((3100 : ℝ) ^ (3 : ℕ)) ≠ 0)] at hh
    exact hh.trans_eq (add_comm _ _)
  have hct : c ≤ t * b := by
    nlinarith [Real.log_le_sub_one_of_pos ht0,
      mul_nonneg (sub_nonneg.mpr ht) (by linarith : 0 ≤ b - 1)]
  have hdiv : (2.50637 : ℝ) / c ≤ 2.50637 / b :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) hbc
  have hdivt : (2.50637 : ℝ) / b ≤ t * (2.50637 / b) :=
    le_mul_of_one_le_left (by positivity) ht
  have hm := mul_le_mul_of_nonneg_left hct (Real.exp_pos Real.eulerMascheroniConstant).le
  change 0 ≤ Real.exp Real.eulerMascheroniConstant * b + 2.50637 / b ∧
    Real.exp Real.eulerMascheroniConstant * c + 2.50637 / c ≤
      t * (Real.exp Real.eulerMascheroniConstant * b + 2.50637 / b)
  exact ⟨by positivity, by nlinarith only [hm, hdiv, hdivt]⟩

def affineSlope (L : ℝ) : ℝ :=
  1 + 4 * Real.log (L / 3100) / (upperLog 3100 - lowerLog 3100)

def affineOffset (L : ℝ) : ℝ :=
  lowerLog L - affineSlope L * lowerLog 3100

theorem affine_source_domain {L : ℝ} (hL : 3100 ≤ L) :
    1 ≤ affineSlope L ∧ affineSlope L ≤ L / 3100 ∧
      affineSlope L * lowerLog 3100 + affineOffset L = lowerLog L ∧
      affineSlope L * upperLog 3100 + affineOffset L = upperLog L := by
  have hd := base_log_domain
  have hs := source_log_scaling hL
  have ht : 1 ≤ L / 3100 := by linarith
  have hl := Real.log_nonneg ht
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < L / 3100)
  have hw : 0 < upperLog 3100 - lowerLog 3100 := by linarith
  have hratio : 4 * Real.log (L / 3100) / (upperLog 3100 - lowerLog 3100) ≤
      Real.log (L / 3100) := (div_le_iff₀ hw).mpr (by nlinarith)
  refine ⟨by unfold affineSlope; exact le_add_of_nonneg_right (by positivity),
    by unfold affineSlope; linarith, ?_, ?_⟩
  · unfold affineOffset
    ring
  · unfold affineOffset affineSlope
    rw [hs.1, hs.2]
    field_simp
    ring

theorem affine_source_shift {L y : ℝ} (hL : 3100 ≤ L)
    (hy : y ∈ Set.Icc (lowerLog 3100) (upperLog 3100)) :
    ∃ k : ℝ, 0 ≤ k ∧ k ≤ 7 ∧
      affineSlope L * y + affineOffset L = y + k * Real.log (L / 3100) := by
  have hd := base_log_domain
  have hw : 0 < upperLog 3100 - lowerLog 3100 := by linarith
  let k := 3 + 4 * (y - lowerLog 3100) / (upperLog 3100 - lowerLog 3100)
  have hdiff : 0 ≤ y - lowerLog 3100 := sub_nonneg.mpr hy.1
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hk7 : k ≤ 7 := by
    dsimp [k]
    have hh : 4 * (y - lowerLog 3100) / (upperLog 3100 - lowerLog 3100) ≤ 4 :=
      (div_le_iff₀ hw).mpr (by linarith [hy.2])
    linarith
  refine ⟨k, hk0, hk7, ?_⟩
  unfold affineOffset affineSlope
  rw [(source_log_scaling hL).1]
  dsimp [k]
  ring

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
