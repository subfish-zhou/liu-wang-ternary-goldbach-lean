import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0471
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11131 : PrimeGap 11119 11131 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11131 :
    (11131 : ℕ).Prime ∧ logScale (11131 : ℚ) = 13 ∧
      (93174892841 : ℤ) = ⌊logCenter (11131 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11131 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11131 : Reach 11131 110077181401501 166123806538 := by
  have hr := row_11131
  have hl := log_bounds hr.1
    (by change logScale (11131 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11119) (T := 109984006508660) (U := 166108882110)
    (by norm_num) (by norm_num) hr.1 gap_11131
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11119

theorem gap_11149 : PrimeGap 11131 11149 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3, 2, 71, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11149 :
    (11149 : ℕ).Prime ∧ logScale (11149 : ℚ) = 13 ∧
      (93191050833 : ℤ) = ⌊logCenter (11149 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11149 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11149 : Reach 11149 110170372452334 166138708208 := by
  have hr := row_11149
  have hl := log_bounds hr.1
    (by change logScale (11149 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11131) (T := 110077181401501) (U := 166123806538)
    (by norm_num) (by norm_num) hr.1 gap_11149
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11131

theorem gap_11159 : PrimeGap 11149 11159 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11159 :
    (11159 : ℕ).Prime ∧ logScale (11159 : ℚ) = 13 ∧
      (93200016228 : ℤ) = ⌊logCenter (11159 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11159 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11159 : Reach 11159 110263572468562 166153597858 := by
  have hr := row_11159
  have hl := log_bounds hr.1
    (by change logScale (11159 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11149) (T := 110170372452334) (U := 166138708208)
    (by norm_num) (by norm_num) hr.1 gap_11159
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11149

theorem gap_11161 : PrimeGap 11159 11161 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11161 :
    (11161 : ℕ).Prime ∧ logScale (11161 : ℚ) = 13 ∧
      (93201808342 : ℤ) = ⌊logCenter (11161 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11161 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11161 : Reach 11161 110356774276904 166168486174 := by
  have hr := row_11161
  have hl := log_bounds hr.1
    (by change logScale (11161 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11159) (T := 110263572468562) (U := 166153597858)
    (by norm_num) (by norm_num) hr.1 gap_11161
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11159

theorem gap_11171 : PrimeGap 11161 11171 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11171 :
    (11171 : ℕ).Prime ∧ logScale (11171 : ℚ) = 13 ∧
      (93210764101 : ℤ) = ⌊logCenter (11171 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11171 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11171 : Reach 11171 110449985041005 166183362494 := by
  have hr := row_11171
  have hl := log_bounds hr.1
    (by change logScale (11171 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11161) (T := 110356774276904) (U := 166168486174)
    (by norm_num) (by norm_num) hr.1 gap_11171
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11161

theorem gap_11173 : PrimeGap 11171 11173 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11173 :
    (11173 : ℕ).Prime ∧ logScale (11173 : ℚ) = 13 ∧
      (93212554291 : ℤ) = ⌊logCenter (11173 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11173 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11173 : Reach 11173 110543197595296 166198237482 := by
  have hr := row_11173
  have hl := log_bounds hr.1
    (by change logScale (11173 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11171) (T := 110449985041005) (U := 166183362494)
    (by norm_num) (by norm_num) hr.1 gap_11173
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11171

theorem gap_11177 : PrimeGap 11173 11177 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11177 :
    (11177 : ℕ).Prime ∧ logScale (11177 : ℚ) = 13 ∧
      (93216133710 : ℤ) = ⌊logCenter (11177 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11177 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11177 : Reach 11177 110636413729006 166213108477 := by
  have hr := row_11177
  have hl := log_bounds hr.1
    (by change logScale (11177 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11173) (T := 110543197595296) (U := 166198237482)
    (by norm_num) (by norm_num) hr.1 gap_11177
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11173

theorem gap_11197 : PrimeGap 11177 11197 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 53, 2, 5, 2, 3, 2, 67, 2, 19, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11197 :
    (11197 : ℕ).Prime ∧ logScale (11197 : ℚ) = 13 ∧
      (93234011608 : ℤ) = ⌊logCenter (11197 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11197 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11197 : Reach 11197 110729647740614 166227954236 := by
  have hr := row_11197
  have hl := log_bounds hr.1
    (by change logScale (11197 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11177) (T := 110636413729006) (U := 166213108477)
    (by norm_num) (by norm_num) hr.1 gap_11197
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11177

#print axioms reach_11197

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
