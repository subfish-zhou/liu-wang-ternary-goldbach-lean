import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block112
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block113
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block114
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block115
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block116
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block117
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block118
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block119
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block120
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block121
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block122
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block123
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block124
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block125
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block126
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block127

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem row_7_0_64 : (607860374423428565822532273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 0 64 := by
  exact block_lower (m := 32) (n := 32) sum_7_0_32 sum_7_32_32 (by norm_num)

theorem row_7_64_64 : (114254120587760653295343231 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 64 64 := by
  exact block_lower (m := 32) (n := 32) sum_7_64_32 sum_7_96_32 (by norm_num)

theorem row_7_0_128 : (433026673639680612275764131 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 0 128 := by
  exact block_lower (m := 64) (n := 64) row_7_0_64 row_7_64_64 (by norm_num)

theorem row_7_128_64 : (286173238032731281681636903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 128 64 := by
  exact block_lower (m := 32) (n := 32) sum_7_128_32 sum_7_160_32 (by norm_num)

theorem row_7_192_64 : (2871169921777708161926769 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 192 64 := by
  exact block_lower (m := 32) (n := 32) sum_7_192_32 sum_7_224_32 (by norm_num)

theorem row_7_128_128 : (291915577876286698005490441 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 128 128 := by
  exact block_lower (m := 64) (n := 64) row_7_128_64 row_7_192_64 (by norm_num)

theorem row_7_0_256 : (404804454487001829421709393 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 0 256 := by
  exact block_lower (m := 128) (n := 128) row_7_0_128 row_7_128_128 (by norm_num)

theorem row_7_256_64 : (51073202688935928662159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 256 64 := by
  exact block_lower (m := 32) (n := 32) sum_7_256_32 sum_7_288_32 (by norm_num)

theorem row_7_320_64 : (85562174563515579461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 320 64 := by
  exact block_lower (m := 32) (n := 32) sum_7_320_32 sum_7_352_32 (by norm_num)

theorem row_7_256_128 : (2557938243174972212081 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 256 128 := by
  exact block_lower (m := 64) (n := 64) row_7_256_64 row_7_320_64 (by norm_num)

theorem row_7_384_64 : (37143284907869583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 384 64 := by
  exact block_lower (m := 32) (n := 32) sum_7_384_32 sum_7_416_32 (by norm_num)

theorem row_7_448_64 : (40675670330973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 448 64 := by
  exact block_lower (m := 32) (n := 32) sum_7_448_32 sum_7_480_32 (by norm_num)

theorem row_7_384_128 : (74327245486070139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 384 128 := by
  exact block_lower (m := 64) (n := 64) row_7_384_64 row_7_448_64 (by norm_num)

theorem row_7_256_256 : (51158839190744930311759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 256 256 := by
  exact block_lower (m := 128) (n := 128) row_7_256_128 row_7_384_128 (by norm_num)

theorem row_7_0_512 : (4048095703709209039147405689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 0 512 := by
  exact block_lower (m := 256) (n := 256) row_7_0_256 row_7_256_256 (by norm_num)

theorem checked_row_7 : (4048095703709209039147405689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ quadLower (7409 / 5 : ℝ) := by
  simpa only [blockSum, rowCell, Nat.zero_add, quadUpper, quadLower, div_one]
    using row_7_0_512

#print axioms checked_row_7

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
