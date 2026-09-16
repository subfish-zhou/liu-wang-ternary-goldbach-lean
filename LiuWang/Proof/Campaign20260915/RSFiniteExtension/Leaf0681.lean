import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0680
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15809 : PrimeGap 15803 15809 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15809 :
    (15809 : ℕ).Prime ∧ logScale (15809 : ℚ) = 13 ∧
      (96683346737 : ℤ) = ⌊logCenter (15809 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15809 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15809 : Reach 15809 157223252902973 172406817719 := by
  have hr := row_15809
  have hl := log_bounds hr.1
    (by change logScale (15809 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15803) (T := 157126569556236) (U := 172395912107)
    (by norm_num) (by norm_num) hr.1 gap_15809
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15803

theorem gap_15817 : PrimeGap 15809 15817 :=
  (primeGap_of_factors (ds := [2, 97, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15817 :
    (15817 : ℕ).Prime ∧ logScale (15817 : ℚ) = 13 ∧
      (96688405865 : ℤ) = ⌊logCenter (15817 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15817 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15817 : Reach 15817 157319941308838 172417718505 := by
  have hr := row_15817
  have hl := log_bounds hr.1
    (by change logScale (15817 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15809) (T := 157223252902973) (U := 172406817719)
    (by norm_num) (by norm_num) hr.1 gap_15817
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15809

theorem gap_15823 : PrimeGap 15817 15823 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15823 :
    (15823 : ℕ).Prime ∧ logScale (15823 : ℚ) = 13 ∧
      (96692198533 : ℤ) = ⌊logCenter (15823 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15823 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15823 : Reach 15823 157416633507371 172428615846 := by
  have hr := row_15823
  have hl := log_bounds hr.1
    (by change logScale (15823 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15817) (T := 157319941308838) (U := 172417718505)
    (by norm_num) (by norm_num) hr.1 gap_15823
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15817

theorem gap_15859 : PrimeGap 15823 15859 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 11, 2, 3, 2, 71, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 83, 2, 3, 2, 101, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15859 :
    (15859 : ℕ).Prime ∧ logScale (15859 : ℚ) = 13 ∧
      (96714924381 : ℤ) = ⌊logCenter (15859 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15859 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15859 : Reach 15859 157513348431752 172439489135 := by
  have hr := row_15859
  have hl := log_bounds hr.1
    (by change logScale (15859 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15823) (T := 157416633507371) (U := 172428615846)
    (by norm_num) (by norm_num) hr.1 gap_15859
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15823

theorem gap_15877 : PrimeGap 15859 15877 :=
  (primeGap_of_factors (ds := [2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15877 :
    (15877 : ℕ).Prime ∧ logScale (15877 : ℚ) = 13 ∧
      (96726267966 : ℤ) = ⌊logCenter (15877 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15877 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15877 : Reach 15877 157610074699718 172450350781 := by
  have hr := row_15877
  have hl := log_bounds hr.1
    (by change logScale (15877 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15859) (T := 157513348431752) (U := 172439489135)
    (by norm_num) (by norm_num) hr.1 gap_15877
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15859

theorem gap_15881 : PrimeGap 15877 15881 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15881 :
    (15881 : ℕ).Prime ∧ logScale (15881 : ℚ) = 13 ∧
      (96728787017 : ℤ) = ⌊logCenter (15881 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15881 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15881 : Reach 15881 157706803486735 172461210375 := by
  have hr := row_15881
  have hl := log_bounds hr.1
    (by change logScale (15881 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15877) (T := 157610074699718) (U := 172450350781)
    (by norm_num) (by norm_num) hr.1 gap_15881
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15877

theorem gap_15887 : PrimeGap 15881 15887 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15887 :
    (15887 : ℕ).Prime ∧ logScale (15887 : ℚ) = 13 ∧
      (96732564403 : ℤ) = ⌊logCenter (15887 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15887 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15887 : Reach 15887 157803536051138 172472066551 := by
  have hr := row_15887
  have hl := log_bounds hr.1
    (by change logScale (15887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15881) (T := 157706803486735) (U := 172461210375)
    (by norm_num) (by norm_num) hr.1 gap_15887
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15881

theorem gap_15889 : PrimeGap 15887 15889 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15889 :
    (15889 : ℕ).Prime ∧ logScale (15889 : ℚ) = 13 ∧
      (96733823215 : ℤ) = ⌊logCenter (15889 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15889 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15889 : Reach 15889 157900269874353 172482922044 := by
  have hr := row_15889
  have hl := log_bounds hr.1
    (by change logScale (15889 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15887) (T := 157803536051138) (U := 172472066551)
    (by norm_num) (by norm_num) hr.1 gap_15889
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15887

#print axioms reach_15889

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
