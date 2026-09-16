import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block003 : List ℕ := [1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987]

theorem complete_Block003 :
    ∀ p ∈ Finset.Ioc 1783 1987, p.Prime ↔ p ∈ primes_Block003 := by
  decide +kernel

theorem row_1787 :
    (1787 : ℕ).Prime ∧ logScale (1787 : ℚ) = 10 ∧
      (74882935125 : ℤ) = ⌊logCenter (1787 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1787 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1787 : Reach 1787 17435467917516 133891382291 := by
  have hr := row_1787
  have hl := log_bounds hr.1
    (by change logScale (1787 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1783) (T := 17360584982391) (U := 133816457063)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1783

theorem row_1789 :
    (1789 : ℕ).Prime ∧ logScale (1789 : ℚ) = 10 ∧
      (74894120809 : ℤ) = ⌊logCenter (1789 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1789 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1789 : Reach 1789 17510362038325 133966265615 := by
  have hr := row_1789
  have hl := log_bounds hr.1
    (by change logScale (1789 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1787) (T := 17435467917516) (U := 133891382291)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1787

theorem row_1801 :
    (1801 : ℕ).Prime ∧ logScale (1801 : ℚ) = 10 ∧
      (74960973425 : ℤ) = ⌊logCenter (1801 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1801 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1801 : Reach 1801 17585323011750 134040691319 := by
  have hr := row_1801
  have hl := log_bounds hr.1
    (by change logScale (1801 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1789) (T := 17510362038325) (U := 133966265615)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1789

theorem row_1811 :
    (1811 : ℕ).Prime ∧ logScale (1811 : ℚ) = 10 ∧
      (75016344552 : ℤ) = ⌊logCenter (1811 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1811 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1811 : Reach 1811 17660339356302 134114746950 := by
  have hr := row_1811
  have hl := log_bounds hr.1
    (by change logScale (1811 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1801) (T := 17585323011750) (U := 134040691319)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1801

theorem row_1823 :
    (1823 : ℕ).Prime ∧ logScale (1823 : ℚ) = 10 ∧
      (75082387720 : ℤ) = ⌊logCenter (1823 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1823 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1823 : Reach 1823 17735421744022 134188355483 := by
  have hr := row_1823
  have hl := log_bounds hr.1
    (by change logScale (1823 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1811) (T := 17660339356302) (U := 134114746950)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1811

theorem row_1831 :
    (1831 : ℕ).Prime ∧ logScale (1831 : ℚ) = 10 ∧
      (75126175420 : ℤ) = ⌊logCenter (1831 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1831 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1831 : Reach 1831 17810547919442 134261682454 := by
  have hr := row_1831
  have hl := log_bounds hr.1
    (by change logScale (1831 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1823) (T := 17735421744022) (U := 134188355483)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1823

theorem row_1847 :
    (1847 : ℕ).Prime ∧ logScale (1847 : ℚ) = 10 ∧
      (75213179775 : ℤ) = ⌊logCenter (1847 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1847 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1847 : Reach 1847 17885761099217 134334413593 := by
  have hr := row_1847
  have hl := log_bounds hr.1
    (by change logScale (1847 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1831) (T := 17810547919442) (U := 134261682454)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1831

theorem row_1861 :
    (1861 : ℕ).Prime ∧ logScale (1861 : ℚ) = 10 ∧
      (75288692540 : ℤ) = ⌊logCenter (1861 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1861 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1861 : Reach 1861 17961049791757 134406636397 := by
  have hr := row_1861
  have hl := log_bounds hr.1
    (by change logScale (1861 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1847) (T := 17885761099217) (U := 134334413593)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1847

theorem row_1867 :
    (1867 : ℕ).Prime ∧ logScale (1867 : ℚ) = 10 ∧
      (75320881409 : ℤ) = ⌊logCenter (1867 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1867 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1867 : Reach 1867 18036370673166 134478665677 := by
  have hr := row_1867
  have hl := log_bounds hr.1
    (by change logScale (1867 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1861) (T := 17961049791757) (U := 134406636397)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1861

theorem row_1871 :
    (1871 : ℕ).Prime ∧ logScale (1871 : ℚ) = 10 ∧
      (75342283236 : ℤ) = ⌊logCenter (1871 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1871 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1871 : Reach 1871 18111712956402 134550579402 := by
  have hr := row_1871
  have hl := log_bounds hr.1
    (by change logScale (1871 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1867) (T := 18036370673166) (U := 134478665677)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1867

theorem row_1873 :
    (1873 : ℕ).Prime ∧ logScale (1873 : ℚ) = 10 ∧
      (75352966998 : ℤ) = ⌊logCenter (1873 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1873 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1873 : Reach 1873 18187065923400 134622454712 := by
  have hr := row_1873
  have hl := log_bounds hr.1
    (by change logScale (1873 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1871) (T := 18111712956402) (U := 134550579402)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1871

theorem row_1877 :
    (1877 : ℕ).Prime ∧ logScale (1877 : ℚ) = 10 ∧
      (75374300339 : ℤ) = ⌊logCenter (1877 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1877 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1877 : Reach 1877 18262440223739 134694215083 := by
  have hr := row_1877
  have hl := log_bounds hr.1
    (by change logScale (1877 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1873) (T := 18187065923400) (U := 134622454712)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1873

theorem row_1879 :
    (1879 : ℕ).Prime ∧ logScale (1879 : ℚ) = 10 ∧
      (75384949968 : ℤ) = ⌊logCenter (1879 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1879 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1879 : Reach 1879 18337825173707 134765937243 := by
  have hr := row_1879
  have hl := log_bounds hr.1
    (by change logScale (1879 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1877) (T := 18262440223739) (U := 134694215083)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1877

theorem row_1889 :
    (1889 : ℕ).Prime ∧ logScale (1889 : ℚ) = 10 ∧
      (75438028649 : ℤ) = ⌊logCenter (1889 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1889 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1889 : Reach 1889 18413263202356 134837317507 := by
  have hr := row_1889
  have hl := log_bounds hr.1
    (by change logScale (1889 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1879) (T := 18337825173707) (U := 134765937243)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1879

theorem row_1901 :
    (1901 : ℕ).Prime ∧ logScale (1901 : ℚ) = 10 ∧
      (75501353398 : ℤ) = ⌊logCenter (1901 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1901 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1901 : Reach 1901 18488764555754 134908284517 := by
  have hr := row_1901
  have hl := log_bounds hr.1
    (by change logScale (1901 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1889) (T := 18413263202356) (U := 134837317507)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1889

theorem row_1907 :
    (1907 : ℕ).Prime ∧ logScale (1907 : ℚ) = 10 ∧
      (75532866029 : ℤ) = ⌊logCenter (1907 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1907 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1907 : Reach 1907 18564297421783 134979065359 := by
  have hr := row_1907
  have hl := log_bounds hr.1
    (by change logScale (1907 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1901) (T := 18488764555754) (U := 134908284517)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1901

theorem row_1913 :
    (1913 : ℕ).Prime ∧ logScale (1913 : ℚ) = 10 ∧
      (75564279668 : ℤ) = ⌊logCenter (1913 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1913 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1913 : Reach 1913 18639861701451 135049661105 := by
  have hr := row_1913
  have hl := log_bounds hr.1
    (by change logScale (1913 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1907) (T := 18564297421783) (U := 134979065359)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1907

theorem row_1931 :
    (1931 : ℕ).Prime ∧ logScale (1931 : ℚ) = 10 ∧
      (75657932798 : ℤ) = ⌊logCenter (1931 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1931 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1931 : Reach 1931 18715519634249 135119635023 := by
  have hr := row_1931
  have hl := log_bounds hr.1
    (by change logScale (1931 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1913) (T := 18639861701451) (U := 135049661105)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1913

theorem row_1933 :
    (1933 : ℕ).Prime ∧ logScale (1933 : ℚ) = 10 ∧
      (75668284766 : ℤ) = ⌊logCenter (1933 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1933 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1933 : Reach 1933 18791187919015 135189572723 := by
  have hr := row_1933
  have hl := log_bounds hr.1
    (by change logScale (1933 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1931) (T := 18715519634249) (U := 135119635023)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1931

theorem row_1949 :
    (1949 : ℕ).Prime ∧ logScale (1949 : ℚ) = 10 ∧
      (75750716969 : ℤ) = ⌊logCenter (1949 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1949 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1949 : Reach 1949 18866938635984 135258971888 := by
  have hr := row_1949
  have hl := log_bounds hr.1
    (by change logScale (1949 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1933) (T := 18791187919015) (U := 135189572723)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1933

theorem row_1951 :
    (1951 : ℕ).Prime ∧ logScale (1951 : ℚ) = 10 ∧
      (75760973380 : ℤ) = ⌊logCenter (1951 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1951 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1951 : Reach 1951 18942699609364 135328335464 := by
  have hr := row_1951
  have hl := log_bounds hr.1
    (by change logScale (1951 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1949) (T := 18866938635984) (U := 135258971888)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1949

theorem row_1973 :
    (1973 : ℕ).Prime ∧ logScale (1973 : ℚ) = 10 ∧
      (75873105034 : ℤ) = ⌊logCenter (1973 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1973 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1973 : Reach 1973 19018572714398 135396960381 := by
  have hr := row_1973
  have hl := log_bounds hr.1
    (by change logScale (1973 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1951) (T := 18942699609364) (U := 135328335464)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1951

theorem row_1979 :
    (1979 : ℕ).Prime ∧ logScale (1979 : ℚ) = 10 ∧
      (75903469429 : ℤ) = ⌊logCenter (1979 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1979 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1979 : Reach 1979 19094476183827 135465411828 := by
  have hr := row_1979
  have hl := log_bounds hr.1
    (by change logScale (1979 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1973) (T := 19018572714398) (U := 135396960381)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1973

theorem row_1987 :
    (1987 : ℕ).Prime ∧ logScale (1987 : ℚ) = 10 ∧
      (75943812399 : ℤ) = ⌊logCenter (1987 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1987 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1987 : Reach 1987 19170419996226 135533622006 := by
  have hr := row_1987
  have hl := log_bounds hr.1
    (by change logScale (1987 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1979) (T := 19094476183827) (U := 135465411828)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1979

#print axioms reach_1987

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
