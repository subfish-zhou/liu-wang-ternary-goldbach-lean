import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block080
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block081
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block082
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block083
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block084
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block085
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block086
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block087
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block088
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block089
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block090
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block091
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block092
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block093
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block094
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block095

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem row_5_0_64 : blockSum (rowCell 5) 0 64 ≤ (1303789125600108083554154509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_5_0_32 sum_5_32_32 (by norm_num)

theorem row_5_64_64 : blockSum (rowCell 5) 64 64 ≤ (676882211177385473703468631 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_5_64_32 sum_5_96_32 (by norm_num)

theorem row_5_0_128 : blockSum (rowCell 5) 0 128 ≤ (6718846815019191873181903557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_5_0_64 row_5_64_64 (by norm_num)

theorem row_5_128_64 : blockSum (rowCell 5) 128 64 ≤ (978987637078545862113169111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_5_128_32 sum_5_160_32 (by norm_num)

theorem row_5_192_64 : blockSum (rowCell 5) 192 64 ≤ (1806524741896988407184529 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_5_192_32 sum_5_224_32 (by norm_num)

theorem row_5_128_128 : blockSum (rowCell 5) 128 128 ≤ (997052884497515746185014401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_5_128_64 row_5_192_64 (by norm_num)

theorem row_5_0_256 : blockSum (rowCell 5) 0 256 ≤ (3857949849758353809683458979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_5_0_128 row_5_128_128 (by norm_num)

theorem row_5_256_64 : blockSum (rowCell 5) 256 64 ≤ (15083779748454134848129 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_5_256_32 sum_5_288_32 (by norm_num)

theorem row_5_320_64 : blockSum (rowCell 5) 320 64 ≤ (120407806769530917817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_5_320_32 sum_5_352_32 (by norm_num)

theorem row_5_256_128 : blockSum (rowCell 5) 256 128 ≤ (37769653274520102579231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_5_256_64 row_5_320_64 (by norm_num)

theorem row_5_384_64 : blockSum (rowCell 5) 384 64 ≤ (50338579672652303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_5_384_32 sum_5_416_32 (by norm_num)

theorem row_5_448_64 : blockSum (rowCell 5) 448 64 ≤ (53487799315567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_5_448_32 sum_5_480_32 (by norm_num)

theorem row_5_384_128 : blockSum (rowCell 5) 384 128 ≤ (100730647144620173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_5_384_64 row_5_448_64 (by norm_num)

theorem row_5_256_256 : blockSum (rowCell 5) 256 256 ≤ (15107881455937469955727 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_5_256_128 row_5_384_128 (by norm_num)

theorem row_5_0_512 : blockSum (rowCell 5) 0 512 ≤ (7715975238923987306716696593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 256) (n := 256) row_5_0_256 row_5_256_256 (by norm_num)

theorem checked_row_5 : quadUpper (1457 / 1 : ℝ) ≤ (7715975238923987306716696593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simpa only [blockSum, rowCell, Nat.zero_add, quadUpper, quadLower, div_one]
    using row_5_0_512

#print axioms checked_row_5

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
