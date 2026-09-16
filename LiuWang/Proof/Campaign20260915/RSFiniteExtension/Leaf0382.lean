import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0381
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9137 : PrimeGap 9133 9137 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9137 :
    (9137 : ℕ).Prime ∧ logScale (9137 : ℚ) = 13 ∧
      (91200873796 : ℤ) = ⌊logCenter (9137 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9137 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9137 : Reach 9137 90161673976908 162602387425 := by
  have hr := row_9137
  have hl := log_bounds hr.1
    (by change logScale (9137 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9133) (T := 90070473103112) (U := 162584591388)
    (by norm_num) (by norm_num) hr.1 gap_9137
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9133

theorem gap_9151 : PrimeGap 9137 9151 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9151 :
    (9151 : ℕ).Prime ∧ logScale (9151 : ℚ) = 13 ∧
      (91216184385 : ℤ) = ⌊logCenter (9151 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9151 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9151 : Reach 9151 90252890161293 162620158178 := by
  have hr := row_9151
  have hl := log_bounds hr.1
    (by change logScale (9151 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9137) (T := 90161673976908) (U := 162602387425)
    (by norm_num) (by norm_num) hr.1 gap_9151
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9137

theorem gap_9157 : PrimeGap 9151 9157 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9157 :
    (9157 : ℕ).Prime ∧ logScale (9157 : ℚ) = 13 ∧
      (91222738897 : ℤ) = ⌊logCenter (9157 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9157 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9157 : Reach 9157 90344112900190 162637919227 := by
  have hr := row_9157
  have hl := log_bounds hr.1
    (by change logScale (9157 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9151) (T := 90252890161293) (U := 162620158178)
    (by norm_num) (by norm_num) hr.1 gap_9157
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9151

theorem gap_9161 : PrimeGap 9157 9161 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9161 :
    (9161 : ℕ).Prime ∧ logScale (9161 : ℚ) = 13 ∧
      (91227106186 : ℤ) = ⌊logCenter (9161 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9161 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9161 : Reach 9161 90435340006376 162655674459 := by
  have hr := row_9161
  have hl := log_bounds hr.1
    (by change logScale (9161 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9157) (T := 90344112900190) (U := 162637919227)
    (by norm_num) (by norm_num) hr.1 gap_9161
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9157

theorem gap_9173 : PrimeGap 9161 9173 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 89, 2, 53, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9173 :
    (9173 : ℕ).Prime ∧ logScale (9173 : ℚ) = 13 ∧
      (91240196621 : ℤ) = ⌊logCenter (9173 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9173 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9173 : Reach 9173 90526580202997 162673408397 := by
  have hr := row_9173
  have hl := log_bounds hr.1
    (by change logScale (9173 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9161) (T := 90435340006376) (U := 162655674459)
    (by norm_num) (by norm_num) hr.1 gap_9173
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9161

theorem gap_9181 : PrimeGap 9173 9181 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 67, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9181 :
    (9181 : ℕ).Prime ∧ logScale (9181 : ℚ) = 13 ∧
      (91248914067 : ℤ) = ⌊logCenter (9181 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9181 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9181 : Reach 9181 90617829117064 162691128812 := by
  have hr := row_9181
  have hl := log_bounds hr.1
    (by change logScale (9181 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9173) (T := 90526580202997) (U := 162673408397)
    (by norm_num) (by norm_num) hr.1 gap_9181
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9173

theorem gap_9187 : PrimeGap 9181 9187 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9187 :
    (9187 : ℕ).Prime ∧ logScale (9187 : ℚ) = 13 ∧
      (91255447168 : ℤ) = ⌊logCenter (9187 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9187 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9187 : Reach 9187 90709084564232 162708839582 := by
  have hr := row_9187
  have hl := log_bounds hr.1
    (by change logScale (9187 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9181) (T := 90617829117064) (U := 162691128812)
    (by norm_num) (by norm_num) hr.1 gap_9187
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9181

theorem gap_9199 : PrimeGap 9187 9199 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 29, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9199 :
    (9199 : ℕ).Prime ∧ logScale (9199 : ℚ) = 13 ∧
      (91268500580 : ℤ) = ⌊logCenter (9199 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9199 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9199 : Reach 9199 90800353064812 162726529171 := by
  have hr := row_9199
  have hl := log_bounds hr.1
    (by change logScale (9199 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9187) (T := 90709084564232) (U := 162708839582)
    (by norm_num) (by norm_num) hr.1 gap_9199
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9187

#print axioms reach_9199

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
