import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block009

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3121 :
    (3121 : ℕ).Prime ∧ logScale (3121 : ℚ) = 11 ∧
      (80459087394 : ℤ) = ⌊logCenter (3121 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3121 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3121 : Reach 3121 30527535674062 143629480064 := by
  have hr := row_3121
  have hl := log_bounds hr.1
    (by change logScale (3121 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3119) (T := 30447076586668) (U := 143583459724)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3119

theorem row_3137 :
    (3137 : ℕ).Prime ∧ logScale (3137 : ℚ) = 11 ∧
      (80510222053 : ℤ) = ⌊logCenter (3137 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3137 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3137 : Reach 3137 30608045896115 143675280281 := by
  have hr := row_3137
  have hl := log_bounds hr.1
    (by change logScale (3137 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3121) (T := 30527535674062) (U := 143629480064)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3121

theorem row_3163 :
    (3163 : ℕ).Prime ∧ logScale (3163 : ℚ) = 11 ∧
      (80592762204 : ℤ) = ⌊logCenter (3163 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3163 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3163 : Reach 3163 30688638658319 143720718384 := by
  have hr := row_3163
  have hl := log_bounds hr.1
    (by change logScale (3163 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3137) (T := 30608045896115) (U := 143675280281)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3137

theorem row_3167 :
    (3167 : ℕ).Prime ∧ logScale (3167 : ℚ) = 11 ∧
      (80605400436 : ℤ) = ⌊logCenter (3167 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3167 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3167 : Reach 3167 30769244058755 143766113431 := by
  have hr := row_3167
  have hl := log_bounds hr.1
    (by change logScale (3167 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3163) (T := 30688638658319) (U := 143720718384)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3163

theorem row_3169 :
    (3169 : ℕ).Prime ∧ logScale (3169 : ℚ) = 11 ∧
      (80611713568 : ℤ) = ⌊logCenter (3169 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3169 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3169 : Reach 3169 30849855772323 143811494149 := by
  have hr := row_3169
  have hl := log_bounds hr.1
    (by change logScale (3169 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3167) (T := 30769244058755) (U := 143766113431)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3167

theorem row_3181 :
    (3181 : ℕ).Prime ∧ logScale (3181 : ℚ) = 11 ∧
      (80649508888 : ℤ) = ⌊logCenter (3181 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3181 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3181 : Reach 3181 30930505281211 143856717890 := by
  have hr := row_3181
  have hl := log_bounds hr.1
    (by change logScale (3181 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3169) (T := 30849855772323) (U := 143811494149)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3169

theorem row_3187 :
    (3187 : ℕ).Prime ∧ logScale (3187 : ℚ) = 11 ∧
      (80668353115 : ℤ) = ⌊logCenter (3187 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3187 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3187 : Reach 3187 31011173634326 143901870658 := by
  have hr := row_3187
  have hl := log_bounds hr.1
    (by change logScale (3187 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3181) (T := 30930505281211) (U := 143856717890)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3181

theorem row_3191 :
    (3191 : ℕ).Prime ∧ logScale (3191 : ℚ) = 11 ∧
      (80680896234 : ℤ) = ⌊logCenter (3191 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3191 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3191 : Reach 3191 31091854530560 143946980963 := by
  have hr := row_3191
  have hl := log_bounds hr.1
    (by change logScale (3191 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3187) (T := 31011173634326) (U := 143901870658)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3187

#print axioms reach_3191

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
