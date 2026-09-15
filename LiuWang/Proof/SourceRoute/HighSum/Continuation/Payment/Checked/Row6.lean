import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block096
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block097
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block098
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block099
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block100
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block101
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block102
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block103
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block104
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block105
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block106
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block107
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block108
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block109
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block110
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block111

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem row_6_0_64 : blockSum (rowCell 6) 0 64 ≤ (810463483107405155522503071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_6_0_32 sum_6_32_32 (by norm_num)

theorem row_6_64_64 : blockSum (rowCell 6) 64 64 ≤ (3634882254250647528025701101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_6_64_32 sum_6_96_32 (by norm_num)

theorem row_6_0_128 : blockSum (rowCell 6) 0 128 ≤ (1111336434339513170887051043 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_6_0_64 row_6_64_64 (by norm_num)

theorem row_6_128_64 : blockSum (rowCell 6) 128 64 ≤ (700952691111356564808085889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_6_128_32 sum_6_160_32 (by norm_num)

theorem row_6_192_64 : blockSum (rowCell 6) 192 64 ≤ (13634119423549657339972019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_6_192_32 sum_6_224_32 (by norm_num)

theorem row_6_128_128 : blockSum (rowCell 6) 128 128 ≤ (178646702633726555537014477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_6_128_64 row_6_192_64 (by norm_num)

theorem row_6_0_256 : blockSum (rowCell 6) 0 256 ≤ (16124789212165496580300819 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_6_0_128 row_6_128_128 (by norm_num)

theorem row_6_256_64 : blockSum (rowCell 6) 256 64 ≤ (11845367023233469500517 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_6_256_32 sum_6_288_32 (by norm_num)

theorem row_6_320_64 : blockSum (rowCell 6) 320 64 ≤ (97464554209766138511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_6_320_32 sum_6_352_32 (by norm_num)

theorem row_6_256_128 : blockSum (rowCell 6) 256 128 ≤ (7415537458797139205137 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_6_256_64 row_6_320_64 (by norm_num)

theorem row_6_384_64 : blockSum (rowCell 6) 384 64 ≤ (8344601102720509 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_6_384_32 sum_6_416_32 (by norm_num)

theorem row_6_448_64 : blockSum (rowCell 6) 448 64 ≤ (9036388383629 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_6_448_32 sum_6_480_32 (by norm_num)

theorem row_6_384_128 : blockSum (rowCell 6) 384 128 ≤ (16698238593824647 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_6_384_64 row_6_448_64 (by norm_num)

theorem row_6_256_256 : blockSum (rowCell 6) 256 256 ≤ (59324383161570082764331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_6_256_128 row_6_384_128 (by norm_num)

theorem row_6_0_512 : blockSum (rowCell 6) 0 512 ≤ (5159991872276120475779026411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 256) (n := 256) row_6_0_256 row_6_256_256 (by norm_num)

theorem checked_row_6 : quadUpper (2945 / 2 : ℝ) ≤ (5159991872276120475779026411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simpa only [blockSum, rowCell, Nat.zero_add, quadUpper, quadLower, div_one]
    using row_6_0_512

#print axioms checked_row_6

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
