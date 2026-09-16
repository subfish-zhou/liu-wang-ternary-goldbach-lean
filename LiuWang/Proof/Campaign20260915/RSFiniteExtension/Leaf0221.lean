import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0220

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5641 :
    (5641 : ℕ).Prime ∧ logScale (5641 : ℚ) = 12 ∧
      (86378166306 : ℤ) = ⌊logCenter (5641 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5641 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5641 : Reach 5641 55293428380933 154012806168 := by
  have hr := row_5641
  have hl := log_bounds hr.1
    (by change logScale (5641 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5639) (T := 55207050214627) (U := 153985503773)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5639

theorem row_5647 :
    (5647 : ℕ).Prime ∧ logScale (5647 : ℚ) = 12 ∧
      (86388797065 : ℤ) = ⌊logCenter (5647 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5647 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5647 : Reach 5647 55379817177998 154040084384 := by
  have hr := row_5647
  have hl := log_bounds hr.1
    (by change logScale (5647 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5641) (T := 55293428380933) (U := 154012806168)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5641

theorem row_5651 :
    (5651 : ℕ).Prime ∧ logScale (5651 : ℚ) = 12 ∧
      (86395877965 : ℤ) = ⌊logCenter (5651 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5651 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5651 : Reach 5651 55466213055963 154067348116 := by
  have hr := row_5651
  have hl := log_bounds hr.1
    (by change logScale (5651 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5647) (T := 55379817177998) (U := 154040084384)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5647

theorem row_5653 :
    (5653 : ℕ).Prime ∧ logScale (5653 : ℚ) = 12 ∧
      (86399416535 : ℤ) = ⌊logCenter (5653 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5653 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5653 : Reach 5653 55552612472498 154094607025 := by
  have hr := row_5653
  have hl := log_bounds hr.1
    (by change logScale (5653 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5651) (T := 55466213055963) (U := 154067348116)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5651

theorem row_5657 :
    (5657 : ℕ).Prime ∧ logScale (5657 : ℚ) = 12 ∧
      (86406489922 : ℤ) = ⌊logCenter (5657 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5657 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5657 : Reach 5657 55639018962420 154121851475 := by
  have hr := row_5657
  have hl := log_bounds hr.1
    (by change logScale (5657 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5653) (T := 55552612472498) (U := 154094607025)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5653

theorem row_5659 :
    (5659 : ℕ).Prime ∧ logScale (5659 : ℚ) = 12 ∧
      (86410024740 : ℤ) = ⌊logCenter (5659 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5659 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5659 : Reach 5659 55725428987160 154149091110 := by
  have hr := row_5659
  have hl := log_bounds hr.1
    (by change logScale (5659 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5657) (T := 55639018962420) (U := 154121851475)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5657

theorem row_5669 :
    (5669 : ℕ).Prime ∧ logScale (5669 : ℚ) = 12 ∧
      (86427680112 : ℤ) = ⌊logCenter (5669 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5669 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5669 : Reach 5669 55811856667272 154176287492 := by
  have hr := row_5669
  have hl := log_bounds hr.1
    (by change logScale (5669 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5659) (T := 55725428987160) (U := 154149091110)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5659

theorem row_5683 :
    (5683 : ℕ).Prime ∧ logScale (5683 : ℚ) = 12 ∧
      (86452345381 : ℤ) = ⌊logCenter (5683 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5683 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5683 : Reach 5683 55898309012653 154203421651 := by
  have hr := row_5683
  have hl := log_bounds hr.1
    (by change logScale (5683 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5669) (T := 55811856667272) (U := 154176287492)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5669

#print axioms reach_5683

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
