import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0181

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4877 :
    (4877 : ℕ).Prime ∧ logScale (4877 : ℚ) = 12 ∧
      (84922855525 : ℤ) = ⌊logCenter (4877 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4877 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4877 : Reach 4877 47755894779466 151448744038 := by
  have hr := row_4877
  have hl := log_bounds hr.1
    (by change logScale (4877 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4871) (T := 47670971923941) (U := 151417690368)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4871

theorem row_4889 :
    (4889 : ℕ).Prime ∧ logScale (4889 : ℚ) = 12 ∧
      (84947430594 : ℤ) = ⌊logCenter (4889 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4889 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4889 : Reach 4889 47840842210060 151479727824 := by
  have hr := row_4889
  have hl := log_bounds hr.1
    (by change logScale (4889 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4877) (T := 47755894779466) (U := 151448744038)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4877

theorem row_4903 :
    (4903 : ℕ).Prime ∧ logScale (4903 : ℚ) = 12 ∧
      (84976025385 : ℤ) = ⌊logCenter (4903 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4903 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4903 : Reach 4903 47925818235445 151510629442 := by
  have hr := row_4903
  have hl := log_bounds hr.1
    (by change logScale (4903 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4889) (T := 47840842210060) (U := 151479727824)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4889

theorem row_4909 :
    (4909 : ℕ).Prime ∧ logScale (4909 : ℚ) = 12 ∧
      (84988255309 : ℤ) = ⌊logCenter (4909 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4909 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4909 : Reach 4909 48010806490754 151541499579 := by
  have hr := row_4909
  have hl := log_bounds hr.1
    (by change logScale (4909 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4903) (T := 47925818235445) (U := 151510629442)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4903

theorem row_4919 :
    (4919 : ℕ).Prime ∧ logScale (4919 : ℚ) = 12 ∧
      (85008605336 : ℤ) = ⌊logCenter (4919 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4919 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4919 : Reach 4919 48095815096090 151572313223 := by
  have hr := row_4919
  have hl := log_bounds hr.1
    (by change logScale (4919 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4909) (T := 48010806490754) (U := 151541499579)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4909

theorem row_4931 :
    (4931 : ℕ).Prime ∧ logScale (4931 : ℚ) = 12 ∧
      (85032970831 : ℤ) = ⌊logCenter (4931 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4931 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4931 : Reach 4931 48180848066921 151603058115 := by
  have hr := row_4931
  have hl := log_bounds hr.1
    (by change logScale (4931 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4919) (T := 48095815096090) (U := 151572313223)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4919

theorem row_4933 :
    (4933 : ℕ).Prime ∧ logScale (4933 : ℚ) = 12 ∧
      (85037025981 : ℤ) = ⌊logCenter (4933 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4933 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4933 : Reach 4933 48265885092902 151633796773 := by
  have hr := row_4933
  have hl := log_bounds hr.1
    (by change logScale (4933 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4931) (T := 48180848066921) (U := 151603058115)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4931

theorem row_4937 :
    (4937 : ℕ).Prime ∧ logScale (4937 : ℚ) = 12 ∧
      (85045131351 : ℤ) = ⌊logCenter (4937 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4937 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4937 : Reach 4937 48350930224253 151664516749 := by
  have hr := row_4937
  have hl := log_bounds hr.1
    (by change logScale (4937 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4933) (T := 48265885092902) (U := 151633796773)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4933

#print axioms reach_4937

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
