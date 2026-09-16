import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0601
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14083 : PrimeGap 14081 14083 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14083 :
    (14083 : ℕ).Prime ∧ logScale (14083 : ℚ) = 13 ∧
      (95527236718 : ℤ) = ⌊logCenter (14083 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14083 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14083 : Reach 14083 139532441259019 170301115865 := by
  have hr := row_14083
  have hl := log_bounds hr.1
    (by change logScale (14083 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14081) (T := 139436914022301) (U := 170289023191)
    (by norm_num) (by norm_num) hr.1 gap_14083
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14081

theorem gap_14087 : PrimeGap 14083 14087 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14087 :
    (14087 : ℕ).Prime ∧ logScale (14087 : ℚ) = 13 ∧
      (95530076618 : ℤ) = ⌊logCenter (14087 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14087 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14087 : Reach 14087 139627971335637 170313205963 := by
  have hr := row_14087
  have hl := log_bounds hr.1
    (by change logScale (14087 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14083) (T := 139532441259019) (U := 170301115865)
    (by norm_num) (by norm_num) hr.1 gap_14087
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14083

theorem gap_14107 : PrimeGap 14087 14107 :=
  (primeGap_of_factors (ds := [2, 73, 2, 3, 2, 17, 2, 5, 2, 3, 2, 23, 2, 59, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14107 :
    (14107 : ℕ).Prime ∧ logScale (14107 : ℚ) = 13 ∧
      (95544264036 : ℤ) = ⌊logCenter (14107 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14107 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14107 : Reach 14107 139723515599673 170325279776 := by
  have hr := row_14107
  have hl := log_bounds hr.1
    (by change logScale (14107 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14087) (T := 139627971335637) (U := 170313205963)
    (by norm_num) (by norm_num) hr.1 gap_14107
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14087

theorem gap_14143 : PrimeGap 14107 14143 :=
  (primeGap_of_factors (ds := [2, 3, 2, 103, 2, 11, 2, 3, 2, 19, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 71, 2, 13, 2, 3, 2, 5, 2, 67, 2, 3, 2, 79, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14143 :
    (14143 : ℕ).Prime ∧ logScale (14143 : ℚ) = 13 ∧
      (95569750776 : ℤ) = ⌊logCenter (14143 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14143 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14143 : Reach 14143 139819085350449 170337323708 := by
  have hr := row_14143
  have hl := log_bounds hr.1
    (by change logScale (14143 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14107) (T := 139723515599673) (U := 170325279776)
    (by norm_num) (by norm_num) hr.1 gap_14143
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14107

theorem gap_14149 : PrimeGap 14143 14149 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14149 :
    (14149 : ℕ).Prime ∧ logScale (14149 : ℚ) = 13 ∧
      (95573992258 : ℤ) = ⌊logCenter (14149 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14149 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14149 : Reach 14149 139914659342707 170349363384 := by
  have hr := row_14149
  have hl := log_bounds hr.1
    (by change logScale (14149 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14143) (T := 139819085350449) (U := 170337323708)
    (by norm_num) (by norm_num) hr.1 gap_14149
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14143

theorem gap_14153 : PrimeGap 14149 14153 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14153 :
    (14153 : ℕ).Prime ∧ logScale (14153 : ℚ) = 13 ∧
      (95576818913 : ℤ) = ⌊logCenter (14153 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14153 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14153 : Reach 14153 140010236161620 170361400507 := by
  have hr := row_14153
  have hl := log_bounds hr.1
    (by change logScale (14153 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14149) (T := 139914659342707) (U := 170349363384)
    (by norm_num) (by norm_num) hr.1 gap_14153
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14149

theorem gap_14159 : PrimeGap 14153 14159 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14159 :
    (14159 : ℕ).Prime ∧ logScale (14159 : ℚ) = 13 ∧
      (95581057399 : ℤ) = ⌊logCenter (14159 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14159 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14159 : Reach 14159 140105817219019 170373433379 := by
  have hr := row_14159
  have hl := log_bounds hr.1
    (by change logScale (14159 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14153) (T := 140010236161620) (U := 170361400507)
    (by norm_num) (by norm_num) hr.1 gap_14159
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14153

theorem gap_14173 : PrimeGap 14159 14173 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14173 :
    (14173 : ℕ).Prime ∧ logScale (14173 : ℚ) = 13 ∧
      (95590940217 : ℤ) = ⌊logCenter (14173 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14173 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14173 : Reach 14173 140201408159236 170385455214 := by
  have hr := row_14173
  have hl := log_bounds hr.1
    (by change logScale (14173 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14159) (T := 140105817219019) (U := 170373433379)
    (by norm_num) (by norm_num) hr.1 gap_14173
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14159

#print axioms reach_14173

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
