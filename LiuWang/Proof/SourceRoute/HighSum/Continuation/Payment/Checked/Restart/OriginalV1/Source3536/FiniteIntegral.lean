import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Cells350
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Cells351
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Cells352
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Cells353
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Cells360
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Cells361
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Cells362
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Cells363
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.EndBounds
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.FiniteFees

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

def grid (i : ℕ) : ℝ := (start : ℝ) + (i : ℝ) / 2

theorem grid_domain (i : ℕ) : 0 < grid i ∧ grid i ≤ grid (i + 1) := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  norm_num [grid, start]
  constructor <;> linarith

def cap35 (i : ℕ) : ℝ :=
  ([125874837587, 97163141606, 74323404216, 56367533309, 42404705485, 31656906245, 23462105089, 17269201596, 12628042200, 9176982449, 6629736462, 4762653458, 3403095070, 2419247855, 1711472629, 1205143657, 844845305, 589752835, 410012776, 283945332, 195908514, 134685366, 92278315, 63016057, 42897513, 29113626, 19701305, 13294645, 8947211, 6005811, 4021336, 2686107] : List ℝ)[i]?.getD 0 / 100000000000000

theorem grid35_paid (i : ℕ) (hi : i < 32) :
    (∫ s in grid i..grid (i + 1), expKernel firstA s) ≤ cap35 i := by
  interval_cases i
  · convert! cell35_0_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_1_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_2_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_3_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_4_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_5_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_6_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_7_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_8_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_9_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_10_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_11_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_12_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_13_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_14_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_15_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_16_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_17_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_18_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_19_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_20_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_21_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_22_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_23_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_24_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_25_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_26_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_27_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_28_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_29_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_30_paid using 1; norm_num [grid, start, expKernel, cap35]
  · convert! cell35_31_paid using 1; norm_num [grid, start, expKernel, cap35]

theorem finite35_paid :
    (∫ s in (start : ℝ)..((start : ℝ) + 16), expKernel firstA s) ≤ fee35 := by
  have hi (i : ℕ) (_hi : i < 32) : IntervalIntegrable (expKernel firstA)
      volume (grid i) (grid (i + 1)) :=
    expKernel_integrable _ (grid_domain i).1 (grid_domain i).2
  have he := intervalIntegral.sum_integral_adjacent_intervals hi
  have hh := Finset.sum_le_sum (s := Finset.range 32) (fun i hi => grid35_paid i (Finset.mem_range.mp hi))
  rw [he] at hh
  norm_num [grid, cap35, fee35, Finset.sum_range_succ] at hh ⊢
  exact hh

theorem primary35_paid :
    (∫ s in (start : ℝ)..(60 : ℝ), expKernel firstA s) ≤ fee35 + 1 / 10000000 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (expKernel_integrable _ (b := (start : ℝ) + 16) (by norm_num [start]) (by norm_num [start]))
    (expKernel_integrable _ (a := (start : ℝ) + 16) (by norm_num [start]) (by norm_num [start]))]
  exact add_le_add finite35_paid first_tail

def cap36 (i : ℕ) : ℝ :=
  ([17383547210, 13937310823, 11057628181, 8686394532, 6759982981, 5214316874, 3988385313, 3026445772, 2279188822, 1704131898, 1265478470, 933637513, 684554546, 498964850, 361644737, 260708798, 186979930, 133443792, 94789113, 67028977, 47194698, 33092395, 23112194, 16080582, 11147461, 7700629, 5301659, 3638219, 2488920, 1697573, 1154489, 782963] : List ℝ)[i]?.getD 0 / 100000000000000

theorem grid36_paid (i : ℕ) (hi : i < 32) :
    (∫ s in grid i..grid (i + 1), expKernel secondA s) ≤ cap36 i := by
  interval_cases i
  · convert! cell36_0_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_1_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_2_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_3_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_4_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_5_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_6_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_7_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_8_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_9_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_10_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_11_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_12_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_13_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_14_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_15_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_16_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_17_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_18_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_19_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_20_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_21_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_22_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_23_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_24_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_25_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_26_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_27_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_28_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_29_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_30_paid using 1; norm_num [grid, start, expKernel, cap36]
  · convert! cell36_31_paid using 1; norm_num [grid, start, expKernel, cap36]

theorem finite36_paid :
    (∫ s in (start : ℝ)..((start : ℝ) + 16), expKernel secondA s) ≤ fee36 := by
  have hi (i : ℕ) (_hi : i < 32) : IntervalIntegrable (expKernel secondA)
      volume (grid i) (grid (i + 1)) :=
    expKernel_integrable _ (grid_domain i).1 (grid_domain i).2
  have he := intervalIntegral.sum_integral_adjacent_intervals hi
  have hh := Finset.sum_le_sum (s := Finset.range 32) (fun i hi => grid36_paid i (Finset.mem_range.mp hi))
  rw [he] at hh
  norm_num [grid, cap36, fee36, Finset.sum_range_succ] at hh ⊢
  exact hh

theorem primary36_paid :
    (∫ s in (start : ℝ)..(60 : ℝ), expKernel secondA s) ≤ fee36 + 1 / 10000000 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (expKernel_integrable _ (b := (start : ℝ) + 16) (by norm_num [start]) (by norm_num [start]))
    (expKernel_integrable _ (a := (start : ℝ) + 16) (by norm_num [start]) (by norm_num [start]))]
  exact add_le_add finite36_paid second_tail

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
