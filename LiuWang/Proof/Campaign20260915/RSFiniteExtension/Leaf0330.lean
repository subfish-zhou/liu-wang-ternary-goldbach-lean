import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block032
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7883 : PrimeGap 7879 7883 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7883 :
    (7883 : ℕ).Prime ∧ logScale (7883 : ℚ) = 12 ∧
      (89724638179 : ℤ) = ⌊logCenter (7883 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7883 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7883 : Reach 7883 77853562693537 160024853209 := by
  have hr := row_7883
  have hl := log_bounds hr.1
    (by change logScale (7883 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7879) (T := 77763838055358) (U := 160004553214)
    (by norm_num) (by norm_num) hr.1 gap_7883
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7879

theorem gap_7901 : PrimeGap 7883 7901 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 53, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7901 :
    (7901 : ℕ).Prime ∧ logScale (7901 : ℚ) = 12 ∧
      (89747446095 : ℤ) = ⌊logCenter (7901 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7901 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7901 : Reach 7901 77943310139632 160045109520 := by
  have hr := row_7901
  have hl := log_bounds hr.1
    (by change logScale (7901 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7883) (T := 77853562693537) (U := 160024853209)
    (by norm_num) (by norm_num) hr.1 gap_7901
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7883

theorem gap_7907 : PrimeGap 7901 7907 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7907 :
    (7907 : ℕ).Prime ∧ logScale (7907 : ℚ) = 12 ∧
      (89755037189 : ℤ) = ⌊logCenter (7907 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7907 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7907 : Reach 7907 78033065176821 160065353020 := by
  have hr := row_7907
  have hl := log_bounds hr.1
    (by change logScale (7907 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7901) (T := 77943310139632) (U := 160045109520)
    (by norm_num) (by norm_num) hr.1 gap_7907
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7901

theorem gap_7919 : PrimeGap 7907 7919 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7919 :
    (7919 : ℕ).Prime ∧ logScale (7919 : ℚ) = 12 ∧
      (89770202110 : ℤ) = ⌊logCenter (7919 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7919 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7919 : Reach 7919 78122835378931 160085568397 := by
  have hr := row_7919
  have hl := log_bounds hr.1
    (by change logScale (7919 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7907) (T := 78033065176821) (U := 160065353020)
    (by norm_num) (by norm_num) hr.1 gap_7919
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7907

theorem gap_7927 : PrimeGap 7919 7927 :=
  (primeGap_of_factors (ds := [2, 89, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7927 :
    (7927 : ℕ).Prime ∧ logScale (7927 : ℚ) = 12 ∧
      (89780299297 : ℤ) = ⌊logCenter (7927 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7927 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7927 : Reach 7927 78212615678228 160105765921 := by
  have hr := row_7927
  have hl := log_bounds hr.1
    (by change logScale (7927 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7919) (T := 78122835378931) (U := 160085568397)
    (by norm_num) (by norm_num) hr.1 gap_7927
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7919

theorem gap_7933 : PrimeGap 7927 7933 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7933 :
    (7933 : ℕ).Prime ∧ logScale (7933 : ℚ) = 12 ∧
      (89787865501 : ℤ) = ⌊logCenter (7933 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7933 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7933 : Reach 7933 78302403543729 160125950713 := by
  have hr := row_7933
  have hl := log_bounds hr.1
    (by change logScale (7933 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7927) (T := 78212615678228) (U := 160105765921)
    (by norm_num) (by norm_num) hr.1 gap_7933
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7927

theorem gap_7937 : PrimeGap 7933 7937 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7937 :
    (7937 : ℕ).Prime ∧ logScale (7937 : ℚ) = 12 ∧
      (89792906459 : ℤ) = ⌊logCenter (7937 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7937 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7937 : Reach 7937 78392196450188 160146127875 := by
  have hr := row_7937
  have hl := log_bounds hr.1
    (by change logScale (7937 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7933) (T := 78302403543729) (U := 160125950713)
    (by norm_num) (by norm_num) hr.1 gap_7937
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7933

theorem gap_7949 : PrimeGap 7937 7949 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7949 :
    (7949 : ℕ).Prime ∧ logScale (7949 : ℚ) = 12 ∧
      (89808014104 : ℤ) = ⌊logCenter (7949 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7949 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7949 : Reach 7949 78482004464292 160166277112 := by
  have hr := row_7949
  have hl := log_bounds hr.1
    (by change logScale (7949 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7937) (T := 78392196450188) (U := 160146127875)
    (by norm_num) (by norm_num) hr.1 gap_7949
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7937

#print axioms reach_7949

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
