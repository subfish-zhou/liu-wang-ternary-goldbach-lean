import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0231

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5869 :
    (5869 : ℕ).Prime ∧ logScale (5869 : ℚ) = 12 ∧
      (86774395374 : ℤ) = ⌊logCenter (5869 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5869 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5869 : Reach 5869 58064249088469 154870856293 := by
  have hr := row_5869
  have hl := log_bounds hr.1
    (by change logScale (5869 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5867) (T := 57977474693095) (U := 154844468346)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5867

theorem row_5879 :
    (5879 : ℕ).Prime ∧ logScale (5879 : ℚ) = 12 ∧
      (86791419552 : ℤ) = ⌊logCenter (5879 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5879 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5879 : Reach 5879 58151040508021 154897203836 := by
  have hr := row_5879
  have hl := log_bounds hr.1
    (by change logScale (5879 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5869) (T := 58064249088469) (U := 154870856293)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5869

theorem row_5881 :
    (5881 : ℕ).Prime ∧ logScale (5881 : ℚ) = 12 ∧
      (86794820913 : ℤ) = ⌊logCenter (5881 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5881 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5881 : Reach 5881 58237835328934 154923546898 := by
  have hr := row_5881
  have hl := log_bounds hr.1
    (by change logScale (5881 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5879) (T := 58151040508021) (U := 154897203836)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5879

theorem row_5897 :
    (5897 : ℕ).Prime ∧ logScale (5897 : ℚ) = 12 ∧
      (86821990228 : ℤ) = ⌊logCenter (5897 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5897 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5897 : Reach 5897 58324657319162 154949822941 := by
  have hr := row_5897
  have hl := log_bounds hr.1
    (by change logScale (5897 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5881) (T := 58237835328934) (U := 154923546898)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5881

theorem row_5903 :
    (5903 : ℕ).Prime ∧ logScale (5903 : ℚ) = 12 ∧
      (86832159721 : ℤ) = ⌊logCenter (5903 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5903 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5903 : Reach 5903 58411489478883 154976076724 := by
  have hr := row_5903
  have hl := log_bounds hr.1
    (by change logScale (5903 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5897) (T := 58324657319162) (U := 154949822941)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5897

theorem row_5923 :
    (5923 : ℕ).Prime ∧ logScale (5923 : ℚ) = 12 ∧
      (86865983531 : ℤ) = ⌊logCenter (5923 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5923 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5923 : Reach 5923 58498355462414 155002246275 := by
  have hr := row_5923
  have hl := log_bounds hr.1
    (by change logScale (5923 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5903) (T := 58411489478883) (U := 154976076724)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5903

theorem row_5927 :
    (5927 : ℕ).Prime ∧ logScale (5927 : ℚ) = 12 ∧
      (86872734586 : ℤ) = ⌊logCenter (5927 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5927 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5927 : Reach 5927 58585228197000 155028402578 := by
  have hr := row_5927
  have hl := log_bounds hr.1
    (by change logScale (5927 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5923) (T := 58498355462414) (U := 155002246275)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5923

theorem row_5939 :
    (5939 : ℕ).Prime ∧ logScale (5939 : ℚ) = 12 ∧
      (86892960448 : ℤ) = ⌊logCenter (5939 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5939 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5939 : Reach 5939 58672121157448 155054510427 := by
  have hr := row_5939
  have hl := log_bounds hr.1
    (by change logScale (5939 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5927) (T := 58585228197000) (U := 155028402578)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5927

#print axioms reach_5939

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
