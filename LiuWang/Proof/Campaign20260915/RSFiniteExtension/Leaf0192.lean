import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0191

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5059 :
    (5059 : ℕ).Prime ∧ logScale (5059 : ℚ) = 12 ∧
      (85289241111 : ℤ) = ⌊logCenter (5059 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5059 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5059 : Reach 5059 49798759208559 152181402953 := by
  have hr := row_5059
  have hl := log_bounds hr.1
    (by change logScale (5059 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5051) (T := 49713469967448) (U := 152151321631)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5051

theorem row_5077 :
    (5077 : ℕ).Prime ∧ logScale (5077 : ℚ) = 12 ∧
      (85324758118 : ℤ) = ⌊logCenter (5077 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5077 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5077 : Reach 5077 49884083966677 152211383529 := by
  have hr := row_5077
  have hl := log_bounds hr.1
    (by change logScale (5077 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5059) (T := 49798759208559) (U := 152181402953)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5059

theorem row_5081 :
    (5081 : ℕ).Prime ∧ logScale (5081 : ℚ) = 12 ∧
      (85332633684 : ℤ) = ⌊logCenter (5081 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5081 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5081 : Reach 5081 49969416600361 152241346400 := by
  have hr := row_5081
  have hl := log_bounds hr.1
    (by change logScale (5081 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5077) (T := 49884083966677) (U := 152211383529)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5077

theorem row_5087 :
    (5087 : ℕ).Prime ∧ logScale (5087 : ℚ) = 12 ∧
      (85344435417 : ℤ) = ⌊logCenter (5087 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5087 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5087 : Reach 5087 50054761035778 152271279815 := by
  have hr := row_5087
  have hl := log_bounds hr.1
    (by change logScale (5087 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5081) (T := 49969416600361) (U := 152241346400)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5081

theorem row_5099 :
    (5099 : ℕ).Prime ∧ logScale (5099 : ℚ) = 12 ∧
      (85367997179 : ℤ) = ⌊logCenter (5099 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5099 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5099 : Reach 5099 50140129032957 152301148642 := by
  have hr := row_5099
  have hl := log_bounds hr.1
    (by change logScale (5099 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5087) (T := 50054761035778) (U := 152271279815)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5087

theorem row_5101 :
    (5101 : ℕ).Prime ∧ logScale (5101 : ℚ) = 12 ∧
      (85371918748 : ℤ) = ⌊logCenter (5101 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5101 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5101 : Reach 5101 50225500951705 152331011613 := by
  have hr := row_5101
  have hl := log_bounds hr.1
    (by change logScale (5101 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5099) (T := 50140129032957) (U := 152301148642)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5099

theorem row_5107 :
    (5107 : ℕ).Prime ∧ logScale (5107 : ℚ) = 12 ∧
      (85383674235 : ℤ) = ⌊logCenter (5107 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5107 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5107 : Reach 5107 50310884625940 152360845341 := by
  have hr := row_5107
  have hl := log_bounds hr.1
    (by change logScale (5107 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5101) (T := 50225500951705) (U := 152331011613)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5101

theorem row_5113 :
    (5113 : ℕ).Prime ∧ logScale (5113 : ℚ) = 12 ∧
      (85395415919 : ℤ) = ⌊logCenter (5113 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5113 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5113 : Reach 5113 50396280041859 152390649889 := by
  have hr := row_5113
  have hl := log_bounds hr.1
    (by change logScale (5113 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5107) (T := 50310884625940) (U := 152360845341)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5107

#print axioms reach_5113

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
