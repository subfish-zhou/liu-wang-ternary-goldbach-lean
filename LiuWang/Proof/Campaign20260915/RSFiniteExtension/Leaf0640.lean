import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block063
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14867 : PrimeGap 14851 14867 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 89, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14867 :
    (14867 : ℕ).Prime ∧ logScale (14867 : ℚ) = 13 ∧
      (96068992672 : ℤ) = ⌊logCenter (14867 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14867 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14867 : Reach 14867 147198516832724 171242791893 := by
  have hr := row_14867
  have hl := log_bounds hr.1
    (by change logScale (14867 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14851) (T := 147102447840052) (U := 171231273577)
    (by norm_num) (by norm_num) hr.1 gap_14867
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14851

theorem gap_14869 : PrimeGap 14867 14869 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14869 :
    (14869 : ℕ).Prime ∧ logScale (14869 : ℚ) = 13 ∧
      (96070337843 : ℤ) = ⌊logCenter (14869 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14869 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14869 : Reach 14869 147294587170567 171254309434 := by
  have hr := row_14869
  have hl := log_bounds hr.1
    (by change logScale (14869 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14867) (T := 147198516832724) (U := 171242791893)
    (by norm_num) (by norm_num) hr.1 gap_14869
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14867

theorem gap_14879 : PrimeGap 14869 14879 :=
  (primeGap_of_factors (ds := [2, 3, 2, 107, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14879 :
    (14879 : ℕ).Prime ∧ logScale (14879 : ℚ) = 13 ∧
      (96077060984 : ℤ) = ⌊logCenter (14879 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14879 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14879 : Reach 14879 147390664231551 171265820008 := by
  have hr := row_14879
  have hl := log_bounds hr.1
    (by change logScale (14879 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14869) (T := 147294587170567) (U := 171254309434)
    (by norm_num) (by norm_num) hr.1 gap_14879
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14869

theorem gap_14887 : PrimeGap 14879 14887 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14887 :
    (14887 : ℕ).Prime ∧ logScale (14887 : ℚ) = 13 ∧
      (96082436244 : ℤ) = ⌊logCenter (14887 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14887 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14887 : Reach 14887 147486746667795 171277325169 := by
  have hr := row_14887
  have hl := log_bounds hr.1
    (by change logScale (14887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14879) (T := 147390664231551) (U := 171265820008)
    (by norm_num) (by norm_num) hr.1 gap_14887
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14879

theorem gap_14891 : PrimeGap 14887 14891 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14891 :
    (14891 : ℕ).Prime ∧ logScale (14891 : ℚ) = 13 ∧
      (96085122792 : ℤ) = ⌊logCenter (14891 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14891 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14891 : Reach 14891 147582831790587 171288828012 := by
  have hr := row_14891
  have hl := log_bounds hr.1
    (by change logScale (14891 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14887) (T := 147486746667795) (U := 171277325169)
    (by norm_num) (by norm_num) hr.1 gap_14891
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14887

theorem gap_14897 : PrimeGap 14891 14897 :=
  (primeGap_of_factors (ds := [2, 53, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14897 :
    (14897 : ℕ).Prime ∧ logScale (14897 : ℚ) = 13 ∧
      (96089151259 : ℤ) = ⌊logCenter (14897 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14897 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14897 : Reach 14897 147678920941846 171300326994 := by
  have hr := row_14897
  have hl := log_bounds hr.1
    (by change logScale (14897 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14891) (T := 147582831790587) (U := 171288828012)
    (by norm_num) (by norm_num) hr.1 gap_14897
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14891

theorem gap_14923 : PrimeGap 14897 14923 :=
  (primeGap_of_factors (ds := [2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14923 :
    (14923 : ℕ).Prime ∧ logScale (14923 : ℚ) = 13 ∧
      (96106589225 : ℤ) = ⌊logCenter (14923 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14923 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14923 : Reach 14923 147775027531071 171311806711 := by
  have hr := row_14923
  have hl := log_bounds hr.1
    (by change logScale (14923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14897) (T := 147678920941846) (U := 171300326994)
    (by norm_num) (by norm_num) hr.1 gap_14923
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14897

theorem gap_14929 : PrimeGap 14923 14929 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14929 :
    (14929 : ℕ).Prime ∧ logScale (14929 : ℚ) = 13 ∧
      (96110609056 : ℤ) = ⌊logCenter (14929 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14929 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14929 : Reach 14929 147871138140127 171323282583 := by
  have hr := row_14929
  have hl := log_bounds hr.1
    (by change logScale (14929 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14923) (T := 147775027531071) (U := 171311806711)
    (by norm_num) (by norm_num) hr.1 gap_14929
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14923

#print axioms reach_14929

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
